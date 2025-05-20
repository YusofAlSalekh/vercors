package lsp

import com.google.gson.JsonPrimitive
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
import vct.options.types.PathOrStd
import vct.parsers.transform.ConstantBlameProvider
import vct.result.VerificationError
import viper.carbon.boogie.Implicits.lift

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
        val options = Options().copy(inputs = List(PathOrStd.Path(path)))
        /*MyLanguageServer.client.logMessage(
          new MessageParams(MessageType.Info, s"Options: ${options.inputs}")
        )*/

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
            /*MyLanguageServer.client.showMessage(new MessageParams(
              MessageType.Error,
              s"Error calling createProgress: ${ex.getMessage}",
            ))*/
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
      /*val parsing = Some(
        Parsing.ofOptions(options, blameProvider).run(options.inputs)
      )*/
      val parsing = Parsing.ofOptions(options, blameProvider).run(options.inputs)

      if (checkCancelled(token))
        return
      report("Resolution")
      val resolution = Resolution.ofOptions(options, blameProvider).run(parsing)
      /*val resolution = Some(
        Resolution.ofOptions(options, blameProvider).run(parsing.get)
      )*/

      if (checkCancelled(token))
        return
      report("Transformation")
      val transformation = Transformation.ofOptions(options, bipResults).run(resolution)
      /*val transformation = Some(
        Transformation.ofOptions(options, bipResults).run(resolution.get)
      )*/

      if (checkCancelled(token))
        return
      report("Backend")
      val backend = Backend.ofOptions(options).run(transformation)
      //val backend = Some(Backend.ofOptions(options).run(transformation.get))

      if (checkCancelled(token))
        return
      report("ExpectedErrors")
      ExpectedErrors.ofOptions(options).run(backend)
      //ExpectedErrors.ofOptions(options).run(backend.get)

      val failures = collector.errs.toSeq
      sendUnexpectedFailureDiagnostics(uri, failures)

      val errorDescriptions = failures.map(_.desc).mkString("\n")
      MyLanguageServer.client.logMessage(new MessageParams(
        MessageType.Error,
        s"Actual verification failures:\n$errorDescriptions",
      ))
      showInfo("Verification completed")
      /*MyLanguageServer.client.showMessage(
        new MessageParams(MessageType.Info, s"Verification completed")
      )*/
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
        /* MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Log,
          s"User error during parsing/resolution: ${ex.getStackTrace
              .mkString("Array(", "\n", ")")}",
        ))*/
       /* MyLanguageServer.client.showMessage(new MessageParams(
          MessageType.Error,
          s"Error during verification: ${ex.getStackTrace.mkString("Array(", "\n", ")")}",
        ))*/
        showError(s"Error during verification: ${ex.getStackTrace.mkString("Array(", "\n", ")")}")
    }
  }

  private def sendUnexpectedFailureDiagnostics(
      uri: String,
      failures: Seq[VerificationFailure],
  ): Unit = {
    val diagnostics = failures.flatMap {
      case vf: WithContractFailure =>
        val mainDiagOpt = nodeFailureToDiagnostic(vf, vf.inlineDesc)
        val causeDiagOpt = nodeFailureToDiagnostic(vf.failure, vf.failure.inlineDescCompletion)

        val diagWithRelated = causeDiagOpt.map { causeDiag =>
          mainDiagOpt.foreach { mainDiag =>
            val related = new DiagnosticRelatedInformation(
              new Location(uri, mainDiag.getRange),
              mainDiag.getMessage
            )
            causeDiag.setRelatedInformation(List(related).asJava)
          }
          causeDiag
        }
        diagWithRelated.toList

      case vf: NodeVerificationFailure =>
        nodeFailureToDiagnostic(vf, vf.inlineDesc).toList

      case vf =>
       /* MyLanguageServer.client.showMessage(new MessageParams(
          MessageType.Error,
          s"Verification failure without position: ${vf.getClass
              .getSimpleName} – ${vf.inlineDesc}",
        ))*/
        showError(s"Verification failure without position: ${vf.getClass
          .getSimpleName} – ${vf.inlineDesc}")
        /*MyLanguageServer.client
          .logMessage(new MessageParams( // think how to handle this
            MessageType.Warning,
            s"Verification failure without position: ${vf.getClass
                .getSimpleName} – ${vf.inlineDesc}",
          ))*/
        Seq.empty
    }
    MyLanguageServer.client
      .publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics.asJava))
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
        /*MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Warning,
          s"No origin found for VerificationError: ${err.getClass.getSimpleName}",
        ))*/
       /* MyLanguageServer.client.showMessage(new MessageParams(
          MessageType.Error,
          s"No origin found for VerificationError: ${err.getClass.getSimpleName}",
        ))*/
        showError(s"No origin found for VerificationError: ${err.getClass.getSimpleName}")
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

  def findOrigin(obj: Any): Option[Origin] = {
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

  def notifyProgress(token: String, value: WorkDoneProgressBegin): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }

  def notifyProgress(token: String, value: WorkDoneProgressReport): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }

  def notifyProgress(token: String, value: WorkDoneProgressEnd): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    MyLanguageServer.client.notifyProgress(params)
  }
}
