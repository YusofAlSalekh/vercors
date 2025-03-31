package lsp

import org.eclipse.lsp4j._
import org.eclipse.lsp4j.services.WorkspaceService

class MyWorkspaceService extends WorkspaceService {
  override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = {
    println("Workspace configuration changed")
  }

  override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = {
    println("Watched files changed")
  }
}
