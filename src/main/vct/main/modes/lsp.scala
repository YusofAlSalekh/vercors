package vct.main.modes

import com.typesafe.scalalogging.LazyLogging
import vct.main.Main
import vct.options.Options
import org.eclipse.lsp4j.launch.LSPLauncher
import lsp.MyLanguageServer

object LSP extends LazyLogging {
  def runOptions(options: Options): Int = {
    if (options.inputs.isEmpty) {
      logger.warn("No inputs given, not running LSP server")
    }

    logger.info("Starting LSP server...")

    val server = new MyLanguageServer()
    val launcher = LSPLauncher.createServerLauncher(server, System.in, System.out)

    server.setClient(launcher.getRemoteProxy)
    launcher.startListening()

    Main.EXIT_CODE_SUCCESS
  }
}
