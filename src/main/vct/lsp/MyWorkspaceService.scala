package lsp

import org.eclipse.lsp4j._
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.{LanguageClient, WorkspaceService}
import vct.col.origin.BlameCollector
import vct.col.rewrite.bip.BIP
import vct.main.stages._
import vct.options.Options
import vct.options.types.PathOrStd
import vct.parsers.transform.ConstantBlameProvider
import vct.result.VerificationError

import java.net.URI
import java.nio.file.Paths
import java.util.concurrent.CompletableFuture

class MyWorkspaceService(var client: LanguageClient) extends WorkspaceService{
  override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = {
    println("Workspace configuration changed")
  }

  override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = {
    println("Watched files changed")
  }

  /*override def executeCommand(params: ExecuteCommandParams): CompletableFuture[AnyRef] = {
    params.getCommand match {
      case "vercors.verify" =>
        CompletableFuture.runAsync(() => {
          val token = "vercors-progress-token"
          val stages = List("Parsing", "Resolution", "Transformation", "Backend", "ExpectedErrors")

          // Request client to create the progress UI
          val createParams = new WorkDoneProgressCreateParams()
          createParams.setToken(token)
          MyLanguageServer.client.createProgress(createParams)

          // Begin progress
          val begin = new WorkDoneProgressBegin()
          begin.setTitle("Verifying")
          begin.setCancellable(false)
          begin.setPercentage(0)
          MyLanguageServer.notifyProgress(token, begin)

          // Simulate progress for each stage
          for ((stage, i) <- stages.zipWithIndex) {
            val report = new WorkDoneProgressReport()
            report.setPercentage((i + 1) * 100 / stages.size)
            report.setMessage(s"Running $stage...")
            MyLanguageServer.notifyProgress(token, report)

            // Simulate delay (replace with actual stage execution later)
            Thread.sleep(500)
          }

          // End progress
          val end = new WorkDoneProgressEnd()
          end.setMessage("Verification finished!")
          MyLanguageServer.notifyProgress(token, end)
        })

        // Respond to client immediately, verification happens async
        CompletableFuture.completedFuture(null)

      case unknown =>
        CompletableFuture.failedFuture(new IllegalArgumentException(s"Unknown command: $unknown"))
    }
  }*/

  override def executeCommand(params: ExecuteCommandParams): CompletableFuture[AnyRef] = {
    params.getCommand match {
      case "vercors.verify" =>
        CompletableFuture.runAsync(() => {
          val uri = params.getArguments.get(0).asInstanceOf[String]
          val path = Paths.get(new URI(uri))
          val token = "vercors-progress-token"

          val createParams = new WorkDoneProgressCreateParams()
          createParams.setToken(token)

          try {
            client.createProgress(createParams)
          } catch {
            case ex: Exception =>
              client.logMessage(new MessageParams(
                MessageType.Error,
                s"Error calling createProgress: ${ex.getMessage}"
              ))
          }

          val options = Options().copy(inputs = List(PathOrStd.Path(path)))
          runVerificationStages(options, token)
        })
        CompletableFuture.completedFuture(null)

      case unknown =>
        CompletableFuture.failedFuture(new IllegalArgumentException(s"Unknown command: $unknown"))
    }
  }

  private def runVerificationStages(options: Options, token: String): Unit = {
    try {
      val collector = BlameCollector()
      val blameProvider = ConstantBlameProvider(collector)

      val begin = new WorkDoneProgressBegin()
      begin.setTitle("Verifying")
      begin.setCancellable(false)
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

      val bipResults = BIP.VerificationResults()

      report("Parsing")
      val parsing = Parsing.ofOptions(options, blameProvider).run(options.inputs)

      report("Resolution")
      val resolution = Resolution.ofOptions(options, blameProvider).run(parsing)

      report("Transformation")
      val transformation = Transformation.ofOptions(options, bipResults).run(resolution)
      /*Parsing.ofOptions(options, blameProvider)
        .thenRun(Resolution.ofOptions(options, blameProvider))
        .thenRun(Transformation.ofOptions(options, bipResults))
        .thenRun(Backend.ofOptions(options))
        .thenRun(ExpectedErrors.ofOptions(options))*/

      report("Backend")
      val backend = Backend.ofOptions(options).run(transformation)

      report("ExpectedErrors")
      ExpectedErrors.ofOptions(options).run(backend)

      val end = new WorkDoneProgressEnd()
      end.setMessage("Verification finished successfully.")
      notifyProgress(token, end)

    } catch {
      case err: VerificationError =>
        val end = new WorkDoneProgressEnd()
        end.setMessage(s"Verification failed: ${err.getMessage}")
        notifyProgress(token, end)

      case ex: Exception =>
        val end = new WorkDoneProgressEnd()
        end.setMessage(s"Unexpected error: ${ex.getMessage}")
        notifyProgress(token, end)
    }
  }

  def notifyProgress(token: String, value: WorkDoneProgressBegin): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    client.notifyProgress(params)
  }

  def notifyProgress(token: String, value: WorkDoneProgressReport): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    client.notifyProgress(params)
  }

  def notifyProgress(token: String, value: WorkDoneProgressEnd): Unit = {
    val params = new ProgressParams()
    params.setToken(token)
    params.setValue(Either.forLeft(value))
    client.notifyProgress(params)
  }
}
