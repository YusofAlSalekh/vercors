package lsp

import vct.options.Options
import vct.parsers.transform.ConstantBlameProvider
import vct.col.origin.BlameCollector
import vct.col.print.Ctx
import vct.result.VerificationError
import java.nio.file.{Paths, Path}
import io.circe.parser._
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.{CompletionItem, _}
import com.typesafe.scalalogging.LazyLogging
import vct.options.types.PathOrStd
import vct.main.stages.{Output, Parsing, Resolution, Transformation}
import vct.parsers.ParseResult
import vct.col.ast.Verification

import java.util
import java.util.Collections
import java.util.concurrent.CompletableFuture
import scala.io.Source
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex
import vct.col.rewrite.Generation

class MyTextDocumentService extends TextDocumentService with LazyLogging {

  private val javaCompletions: java.util.List[CompletionItem] = loadCompletions(
    "language-server-java-c-matches.json"
  )
  private val pvlCompletions: java.util.List[CompletionItem] = loadCompletions(
    "language-server-pvl-matches.json"
  )

  var parsingResults: Option[ParseResult[Nothing]] = None
  var resolutionResults: Option[Verification[_ <: Generation]] = None


  override def completion(params: CompletionParams): CompletableFuture[
    Either[java.util.List[CompletionItem], CompletionList]
  ] = {
    val uri = params.getTextDocument.getUri
    val items: java.util.List[CompletionItem] =
      if (uri.endsWith(".pvl"))
        pvlCompletions
      else if (uri.endsWith(".java"))
        javaCompletions
      else
        Collections.emptyList()

    CompletableFuture.completedFuture(Either.forLeft(items))
  }

  def resolveCompletion(
      item: CompletionItem
  ): CompletableFuture[CompletionItem] = CompletableFuture.completedFuture(item)

  override def didOpen(params: DidOpenTextDocumentParams): Unit = {
    println(s"Document opened: ${params.getTextDocument.getUri}")
  }

  override def didChange(params: DidChangeTextDocumentParams): Unit = {
    logger.info(s"Document changed: ${params.getTextDocument.getUri}")
    val text = params.getContentChanges.get(0).getText
    val diagnostics = validateText(text)
    val paramsDiag =
      new PublishDiagnosticsParams(
        params.getTextDocument.getUri,
        diagnostics.asJava,
      )
    if (MyLanguageServer.client != null) {
      MyLanguageServer.client.publishDiagnostics(paramsDiag)
    }
  }

  override def didClose(params: DidCloseTextDocumentParams): Unit = {
    println(s"Document closed: ${params.getTextDocument.getUri}")
  }

  override def hover(params: HoverParams): CompletableFuture[Hover] = null

  override def codeAction(
      params: CodeActionParams
  ): CompletableFuture[util.List[Either[Command, CodeAction]]] = null

  override def documentSymbol(params: DocumentSymbolParams) = null

  /*override def didSave(params: DidSaveTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    val path = Paths.get(new java.net.URI(uri))

    logger.info(s"Document saved: $uri")
    MyLanguageServer.client.logMessage(new MessageParams(
      MessageType.Log,
      s"Document saved: ${params.getTextDocument.getUri}",
    ))

    val options = Options().copy(inputs = List(PathOrStd.Path(path)))

    val collector = BlameCollector()
    val blameProvider = ConstantBlameProvider(collector)

    val result = Parsing.ofOptions(options, blameProvider)
      .thenRun(Resolution.ofOptions(options, blameProvider)).run(options.inputs)

      result match {
        case Left(err: VerificationError.UserError) =>
          logger.error(err.text)
          MyLanguageServer.client.logMessage(new MessageParams(
            MessageType.Log,
            s"Parsing/Resolution error: ${err.text}",
          ))
        case Left(err: VerificationError.SystemError) =>
          logger.error("System error during parsing/resolution", err)
          MyLanguageServer.client.logMessage(new MessageParams(
            MessageType.Log,
            s"Verification error: ${err.text}",
          ))
        case Right(_) =>
          logger.info("Parsing and resolution succeeded")
          MyLanguageServer.client.logMessage(new MessageParams(
            MessageType.Log,
            "Parsing and resolution succeeded",
          ))
      }
    }*/

  override def didSave(params: DidSaveTextDocumentParams): Unit = {

    val uri = params.getTextDocument.getUri
    val path = Paths.get(new java.net.URI(uri))

    logger.info(s"Document saved: $uri")
    MyLanguageServer.client.logMessage(new MessageParams(
      MessageType.Log,
      s"Document saved: ${params.getTextDocument.getUri}",
    ))

    val options = Options().copy(inputs = List(PathOrStd.Path(path)))

    try {
      val collector = BlameCollector()
      val blameProvider = ConstantBlameProvider(collector)

      parsingResugit atatus lts = Some(Parsing.ofOptions(options, blameProvider)
        .run(options.inputs))
      resolutionResults = Some(Resolution.ofOptions(options, blameProvider)
        .run(parsingResults.get))

    } catch {
      case err: VerificationError.SystemError =>
        logger.error("System error during parsing/resolution", err)
        MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Error,
          s"Verification error: ${err.text}",
        ))
    }
  }

  private def validateText(text: String): List[Diagnostic] = {
    val pattern: Regex = "\\b[A-Z]{2,}\\b".r
    pattern.findAllMatchIn(text).map { m =>
      val diagnostic = new Diagnostic()
      diagnostic.setSeverity(DiagnosticSeverity.Warning)
      diagnostic.setMessage(s"${m.matched} is all uppercase.")
      diagnostic
        .setRange(new Range(new Position(0, m.start), new Position(0, m.end)))
      diagnostic
    }.toList
  }

  private def loadCompletions(
      fileName: String
  ): java.util.List[CompletionItem] = {
    try {
      val source = Source.fromResource(fileName)
      val jsonString = source.getLines().mkString
      source.close()
      parse(jsonString) match {
        case Right(json) =>
          json.as[List[Map[String, String]]] match {
            case Right(items) =>
              items.flatMap(_.get("match").map(s => new CompletionItem(s)))
                .asJava
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

  override def definition(params: DefinitionParams): CompletableFuture[
    Either[util.List[_ <: Location], util.List[_ <: LocationLink]]
  ] = {
    val uri = params.getTextDocument.getUri
    println(
      s"Go to definition requested in file: $uri, at position: ${params.getPosition}"
    )

    MyLanguageServer.client.logMessage(new MessageParams(
      MessageType.Log,
      s"Parsing and resolution succeeded. Resolution output: ${resolutionResults.get.tasks.size}",
    ))

    val range = new Range(new Position(18, 0), new Position(18, 5))

    val location = new Location(uri, range)

    CompletableFuture
      .completedFuture(Either.forLeft(Collections.singletonList(location)))
  }
}
