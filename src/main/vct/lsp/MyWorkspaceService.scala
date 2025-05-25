package lsp

import com.google.gson.{JsonElement, JsonPrimitive}
import hre.progress.TaskRegistry
import hre.progress.task.RootTask
import lsp.MyLanguageServer.cancelledTokens
import org.eclipse.lsp4j._
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.WorkspaceService
import vct.col.ast.Node
import vct.col.origin._
import vct.col.rewrite.bip.BIP
import vct.lsp.LspMessages._
import vct.main.stages._
import vct.options.Options
import vct.parsers.transform.ConstantBlameProvider
import vct.result.VerificationError

import java.net.URI
import java.nio.file.Paths
import java.util.concurrent.CompletableFuture
import scala.jdk.CollectionConverters._
import scala.language.reflectiveCalls

class MyWorkspaceService extends WorkspaceService {

  override def didChangeConfiguration(
      params: DidChangeConfigurationParams
  ): Unit = { println("Workspace configuration changed") }

  override def didChangeWatchedFiles(
      params: DidChangeWatchedFilesParams
  ): Unit = { println("Watched files changed") }

  override def executeCommand(
      params: ExecuteCommandParams
  ): CompletableFuture[AnyRef] = {
    params.getCommand match {
      case "vercors.lspVerify" =>
        val uri =
          params.getArguments.get(0).asInstanceOf[JsonPrimitive].getAsString
        val path = Paths.get(new URI(uri))

        val syntheticArgs = collection.mutable.ListBuffer("--verify")
        if (params.getArguments.size > 1) {
          val arg1 = params.getArguments.get(1)
          if (arg1.isInstanceOf[JsonElement]) {
            val json = arg1.asInstanceOf[JsonElement]
            if (json.isJsonObject) {
              val obj = json.getAsJsonObject

              def addArray(key: String): Unit =
                if (obj.has(key)) {
                  obj.get(key) match {
                    case arr if arr.isJsonArray =>
                      arr.getAsJsonArray.iterator().asScala.foreach { elem =>
                        syntheticArgs += elem.getAsString
                      }
                    case str if str.isJsonPrimitive =>
                      str.getAsString.trim.split("\\s+")
                        .foreach(syntheticArgs += _)
                    case _ => // do nothing
                  }
                }

              def addSingleFlagWithValue(flag: String, key: String): Unit =
                if (obj.has(key)) {
                  val value = obj.get(key).getAsString
                  syntheticArgs += flag
                  syntheticArgs += value
                }

              addArray("flags")
              addArray("customFlags")
              addArray("rawArgs")

              addSingleFlagWithValue("--backend", "backend")
            }
          }
        }
        syntheticArgs += path.toString

        val options = vct.options.Options.parse(syntheticArgs.toArray)
          .getOrElse(
            throw new IllegalArgumentException("Failed to parse options")
          )

        // val options = Options().copy(inputs = List(PathOrStd.Path(path)))
        val rawToken = params.getWorkDoneToken
        val token =
          if (rawToken.isLeft)
            rawToken.getLeft
          else
            rawToken.getRight.toString
        val createParams = new WorkDoneProgressCreateParams()
        createParams.setToken(token)

        try { MyLanguageServer.client.createProgress(createParams) }
        catch {
          case ex: Exception =>
            showError(s"Error calling createProgress: ${ex.getMessage}")
        }

        val rootTask = TaskRegistry.getRootTask
        CompletableFuture
          .runAsync(() => runVerificationStages(options, token, uri, rootTask))
          .thenApply(_ => null)

      case unknown =>
        CompletableFuture.failedFuture(new IllegalArgumentException(
          s"Unknown command: $unknown"
        ))
    }
  }

  private def runVerificationStages(
      options: Options,
      token: String,
      uri: String,
      rootTask: RootTask,
  ): Unit = {
    TaskRegistry().install()
    rootTask.start()

    try {
      val collector = BlameCollector()
      val blameProvider = ConstantBlameProvider(collector)
      val bipResults = BIP.VerificationResults()

      val begin = new WorkDoneProgressBegin()
      begin.setTitle("Verifying")
      begin.setCancellable(true)
      begin.setPercentage(0)
      notifyProgress(token, begin)

      val totalStages = 5
      var currentStage = 0

      def report(stageName: String): Unit = {
        currentStage += 1
        val report = new WorkDoneProgressReport()
        report.setMessage(s"Running $stageName...")
        report.setPercentage(currentStage * 100 / totalStages)
        notifyProgress(token, report)
      }

      if (checkCancelled(token))
        return
      report("Parsing")
      val parsing = Parsing.ofOptions(options, blameProvider)
        .run(options.inputs)

      if (checkCancelled(token))
        return
      report("Resolution")
      val resolution = Resolution.ofOptions(options, blameProvider).run(parsing)

      if (checkCancelled(token))
        return
      report("Transformation")
      val transformation = Transformation.ofOptions(options, bipResults)
        .run(resolution)

      if (checkCancelled(token))
        return
      report("Backend")
      val backend = Backend.ofOptions(options).run(transformation)

      if (checkCancelled(token))
        return
      report("ExpectedErrors")
      ExpectedErrors.ofOptions(options).run(backend)

      val failures = collector.errs.toSeq
      sendUnexpectedFailureDiagnostics(uri, failures)

      val errorDescriptions = failures.map(_.desc).mkString("\n")
      MyLanguageServer.client.logMessage(new MessageParams(
        MessageType.Error,
        s"Actual verification failures:\n$errorDescriptions",
      ))

      showInfo("Verification completed")
    } catch {
      case err: VerificationError =>
        val end = new WorkDoneProgressEnd()
        end.setMessage(s"Verification failed: ${err.getMessage}")
        notifyProgress(token, end)
        sendVerificationErrorDiagnostic(uri, err)

      case ex: Exception =>
        val end = new WorkDoneProgressEnd()
        end.setMessage(s"Unexpected error: ${ex.getMessage}")
        notifyProgress(token, end)
        showError(
          s"Error during verification: ${ex.getStackTrace.mkString("Array(", "\n", ")")}"
        )
    }
  }

  private def sendUnexpectedFailureDiagnostics(
      uri: String,
      failures: Seq[VerificationFailure],
  ): Unit = {
    val diagnostics = failures.flatMap {
      case vf: WithContractFailure =>
        val mainDiagOpt = nodeFailureToDiagnostic(vf, vf.inlineDesc)
        val causeDiagOpt = nodeFailureToDiagnostic(
          vf.failure,
          vf.failure.inlineDescCompletion,
        )

        val diagWithRelated = mainDiagOpt.map { mainDiag =>
          causeDiagOpt.foreach { causeDiag =>
            val related =
              new DiagnosticRelatedInformation(
                new Location(uri, causeDiag.getRange),
                causeDiag.getMessage,
              )
            mainDiag.setRelatedInformation(List(related).asJava)
          }
          mainDiag
        }
        diagWithRelated.toList

      case vf: NodeVerificationFailure =>
        nodeFailureToDiagnostic(vf, vf.inlineDesc) match {
          case Some(diag) => List(diag)
          case None =>
            showError("NodeVerificationFailure had no usable origin")
            Nil
        }

      case vf: MultiOriginFailure =>
        val mainDiagOpt = vf.originsWithMessages.headOption.flatMap {
          case (origin, _) => originToDiagnostic(origin, vf.inlineDesc)
        }
        val related = vf.originsWithMessages.drop(1)
          .flatMap { case (origin, msg) =>
            originToDiagnostic(origin, msg).map { diag =>
              new DiagnosticRelatedInformation(
                new Location(uri, diag.getRange),
                diag.getMessage,
              )
            }
          }

        mainDiagOpt match {
          case Some(mainDiag) =>
            if (related.nonEmpty) {
              mainDiag.setRelatedInformation(related.asJava)
            }
            List(mainDiag)
          case None =>
            showError("MultiOriginFailure had no usable origin")
            Nil
        }

      case SYCLKernelLambdaFailure(inner) =>
        sendUnexpectedFailureDiagnostics(uri, Seq(inner))
        Nil

      case eef: ExpectedErrorFailure =>
        originToDiagnostic(eef.err.errorRegion, eef.inlineDesc) match {
          case Some(diag) => List(diag)
          case None =>
            showError("ExpectedErrorFailure had no usable origin")
            Nil
        }

      case vf =>
        showError(
          s"Unhandled verification failure: ${vf.getClass.getSimpleName} – ${vf.inlineDesc}"
        )
        Seq.empty
    }
    MyLanguageServer.client
      .publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics.asJava))
  }

  private def originToDiagnostic(
      origin: Origin,
      message: String,
  ): Option[Diagnostic] = {
    origin.find[PositionRange].flatMap {
      case PositionRange(startLine, endLine, Some((startCol, endCol))) =>
        Some(new Diagnostic(
          new Range(
            new Position(startLine, startCol),
            new Position(endLine, endCol),
          ),
          message,
          DiagnosticSeverity.Error,
          "VerCors",
        ))
      case PositionRange(startLine, endLine, None) =>
        Some(new Diagnostic(
          new Range(new Position(startLine, 0), new Position(endLine, 0)),
          message,
          DiagnosticSeverity.Error,
          "VerCors",
        ))
    }
  }

  private def nodeFailureToDiagnostic(
      vf: { def node: vct.col.ast.Node[_] },
      message: String,
  ): Option[Diagnostic] = {
    vf.node.o.find[PositionRange].flatMap { pos =>
      pos.startEndColIdx.map { case (startCol, endCol) =>
        val diag = new Diagnostic()
        diag.setSeverity(DiagnosticSeverity.Error)
        diag.setMessage(message)
        diag.setSource("VerCors")
        diag.setRange(new Range(
          new Position(pos.startLineIdx, startCol),
          new Position(pos.endLineIdx, endCol),
        ))
        diag
      }
    }
  }

  private def sendVerificationErrorDiagnostic(
      uri: String,
      err: VerificationError,
  ): Unit = {
    findOrigin(err) match {
      case Some(origin) =>
        val range = originToRange(origin)
        val diagnostic: Diagnostic = createVerificationErrorDiagnostic(
          err,
          range,
        )
        MyLanguageServer.client.publishDiagnostics(
          new PublishDiagnosticsParams(uri, List(diagnostic).asJava)
        )

      case None =>
        showError(
          s"No origin found for VerificationError: ${err.getClass.getSimpleName}"
        )
    }
  }

  private def originToRange(origin: Origin) = {
    origin.find[PositionRange].map {
      case PositionRange(startLine, endLine, Some((startCol, endCol))) =>
        new Range(
          new Position(startLine, startCol),
          new Position(endLine, endCol),
        )
      case PositionRange(startLine, endLine, None) =>
        new Range(new Position(startLine, 0), new Position(endLine, 0))
    }.getOrElse(new Range(new Position(0, 0), new Position(0, 0)))
  }

  private def createVerificationErrorDiagnostic(
      err: VerificationError,
      range: Range,
  ) = {
    val diagnostic = new Diagnostic()
    diagnostic.setSeverity(DiagnosticSeverity.Error)
    diagnostic.setRange(range)
    diagnostic.setSource("VerCors")
    diagnostic.setMessage(err.text)
    diagnostic
  }

  private def findOrigin(obj: Any): Option[Origin] = {
    def tryGet(methodName: String): Option[Origin] = {
      obj.getClass.getMethods.find(m =>
        m.getName == methodName && m.getParameterCount == 0 &&
          classOf[Origin].isAssignableFrom(m.getReturnType)
      ).flatMap { method =>
        try Some(method.invoke(obj).asInstanceOf[Origin])
        catch { case _: Throwable => None }
      }
    }

    tryGet("o").orElse(tryGet("origin")).orElse {
      obj.getClass.getDeclaredFields
        .find(f => classOf[Origin].isAssignableFrom(f.getType))
        .flatMap { field =>
          field.setAccessible(true)
          try Some(field.get(obj).asInstanceOf[Origin])
          catch { case _: Throwable => None }
        }
    }.orElse {
      obj.getClass.getDeclaredFields
        .find(f => classOf[Node[_]].isAssignableFrom(f.getType))
        .flatMap { field =>
          field.setAccessible(true)
          try {
            val node = field.get(obj).asInstanceOf[Node[_]]
            Some(node.o)
          } catch { case _: Throwable => None }
        }
    }
  }

  private def checkCancelled(token: String): Boolean = {
    if (cancelledTokens.contains(token)) {
      cancelledTokens.remove(token)
      val end = new WorkDoneProgressEnd()
      end.setMessage(s"Verification cancelled by user")
      notifyProgress(token, end)
      true
    } else
      false
  }

  private def notifyProgress(
      token: String,
      value: WorkDoneProgressBegin,
  ): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }

  private def notifyProgress(
      token: String,
      value: WorkDoneProgressReport,
  ): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }

  private def notifyProgress(
      token: String,
      value: WorkDoneProgressEnd,
  ): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }
}
