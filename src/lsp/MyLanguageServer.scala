package lsp

import org.eclipse.lsp4j._
import org.eclipse.lsp4j.services.{LanguageClient, LanguageServer, TextDocumentService, WorkspaceService}
import java.util.concurrent.CompletableFuture

class MyLanguageServer extends LanguageServer {
  private val textDocumentService = new MyTextDocumentService()
  private val workspaceService = new MyWorkspaceService()
  MyLanguageServer.client = null

  def setClient(client: LanguageClient): Unit = {
    MyLanguageServer.client = client
  }

  override def initialize(params: InitializeParams): CompletableFuture[InitializeResult] = {
    val capabilities = new ServerCapabilities()
    capabilities.setTextDocumentSync(TextDocumentSyncKind.Incremental)
    capabilities.setCompletionProvider(new CompletionOptions(true, java.util.Collections.emptyList()))
    capabilities.setDefinitionProvider(true)
    capabilities.setReferencesProvider(true)
    capabilities.setHoverProvider(true)
    capabilities.setDocumentSymbolProvider(true)
    capabilities.setCodeActionProvider(true)

    CompletableFuture.completedFuture(new InitializeResult(capabilities))
  }

  override def shutdown(): CompletableFuture[AnyRef] = CompletableFuture.completedFuture(null)

  override def exit(): Unit = System.exit(0)

  override def getTextDocumentService: TextDocumentService = textDocumentService

  override def getWorkspaceService: WorkspaceService = workspaceService
}

object MyLanguageServer {
  var client: LanguageClient = _
}
