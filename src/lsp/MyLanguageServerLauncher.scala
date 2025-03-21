package lsp

import org.eclipse.lsp4j.launch.LSPLauncher

object MyLanguageServerLauncher {
  def main(args: Array[String]): Unit = {
    val server = new MyLanguageServer()
    val launcher = LSPLauncher.createServerLauncher(server, System.in, System.out)
    server.setClient(launcher.getRemoteProxy)
    launcher.startListening()
  }
}
