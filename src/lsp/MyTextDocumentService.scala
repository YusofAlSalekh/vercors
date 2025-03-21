package lsp

import io.circe.parser._
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.{CompletionItem, _}

import java.util.Collections
import java.util.concurrent.CompletableFuture
import scala.io.Source
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

class MyTextDocumentService extends TextDocumentService {

  private val javaCompletions: java.util.List[CompletionItem] = loadCompletions("language-server-java-c-matches.json")
  private val pvlCompletions: java.util.List[CompletionItem] = loadCompletions("language-server-pvl-matches.json")

  override def completion(params: CompletionParams): CompletableFuture[Either[java.util.List[CompletionItem], CompletionList]] = {
    val uri = params.getTextDocument.getUri
    val items: java.util.List[CompletionItem] =
      if (uri.endsWith(".pvl")) pvlCompletions
      else if (uri.endsWith(".java")) javaCompletions
      else Collections.emptyList()

    CompletableFuture.completedFuture(Either.forLeft(items))
  }

  def resolveCompletion(item: CompletionItem): CompletableFuture[CompletionItem] =
    CompletableFuture.completedFuture(item)

  override def didOpen(params: DidOpenTextDocumentParams): Unit = {
    println(s"Document opened: ${params.getTextDocument.getUri}")
  }

  override def didChange(params: DidChangeTextDocumentParams): Unit = {
    println(s"Document changed: ${params.getTextDocument.getUri}")
    val text = params.getContentChanges.get(0).getText
    val diagnostics = validateText(text)
    val paramsDiag = new PublishDiagnosticsParams(params.getTextDocument.getUri, diagnostics.asJava)
    if (MyLanguageServer.client != null) {
      MyLanguageServer.client.publishDiagnostics(paramsDiag)
    }
  }

  override def didClose(params: DidCloseTextDocumentParams): Unit = {
    println(s"Document closed: ${params.getTextDocument.getUri}")
  }

  override def didSave(params: DidSaveTextDocumentParams): Unit = {
    println(s"Document saved: ${params.getTextDocument.getUri}")
  }

  private def validateText(text: String): List[Diagnostic] = {
    val pattern: Regex = "\\b[A-Z]{2,}\\b".r
    pattern.findAllMatchIn(text).map { m =>
      val diagnostic = new Diagnostic()
      diagnostic.setSeverity(DiagnosticSeverity.Warning)
      diagnostic.setMessage(s"${m.matched} is all uppercase.")
      diagnostic.setRange(new Range(new Position(0, m.start), new Position(0, m.end)))
      diagnostic
    }.toList
  }

  private def loadCompletions(fileName: String): java.util.List[CompletionItem] = {
    try {
      val source = Source.fromResource(fileName)
      val jsonString = source.getLines().mkString
      source.close()
      parse(jsonString) match {
        case Right(json) =>
          json.as[List[Map[String, String]]] match {
            case Right(items) =>
              items.flatMap(_.get("match").map(s => new CompletionItem(s))).asJava
            case Left(error) =>
              println(s"Error parsing matches: ${error.getMessage}")
              Collections.emptyList()
          }
        case Left(error) =>
          println(s"Error parsing JSON: ${error.getMessage}")
          Collections.emptyList()
      }
    } catch {
      case e: Exception =>
        println(s"Exception loading completions: ${e.getMessage}")
        Collections.emptyList()
    }
  }
}
