package lsp

import com.microsoft.z3.Expr
import vct.options.Options
import vct.parsers.transform.ConstantBlameProvider
import vct.col.origin.{BlameCollector, PositionRange}
import vct.col.print.Ctx
import vct.result.VerificationError

import java.nio.file.{Path, Paths}
import io.circe.parser._
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.{CompletionItem, _}
import com.typesafe.scalalogging.LazyLogging
import vct.options.types.PathOrStd
import vct.main.stages.{Output, Parsing, Resolution, Transformation}
import vct.parsers.ParseResult
import vct.col.ast.{Local, Node, Verification}

import java.util
import java.util.Collections
import java.util.concurrent.CompletableFuture
import scala.io.Source
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex
import vct.col.rewrite.Generation

import scala.collection.immutable.TreeMap
import scala.collection.mutable

class MyTextDocumentService extends TextDocumentService with LazyLogging {

  private val javaCompletions: java.util.List[CompletionItem] = loadCompletions(
    "language-server-java-c-matches.json"
  )
  private val pvlCompletions: java.util.List[CompletionItem] = loadCompletions(
    "language-server-pvl-matches.json"
  )

  var parsingResults: Option[ParseResult[Nothing]] = None
  var resolutionResults: Option[Verification[_ <: Generation]] = None
  var originMap: TreeMap[(Int, Int, Int), (Int, Int, Int)] = TreeMap.empty


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

      parsingResults = Some(Parsing.ofOptions(options, blameProvider)
        .run(options.inputs))
      resolutionResults = Some(Resolution.ofOptions(options, blameProvider)
        .run(parsingResults.get))

      val resolvedProgram = resolutionResults.get.tasks.head.program
      val locals: Seq[Local[_]] = LocalCollector.collectLocals(resolvedProgram)
      originMap = TreeMap.from(LocalCollector.hashLocalOrigins(locals))

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

  /*override def definition(params: DefinitionParams): CompletableFuture[
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
  }*/
  /*override def definition(params: DefinitionParams): CompletableFuture[
    Either[util.List[_ <: Location], util.List[_ <: LocationLink]]
  ] = {
    val uri = params.getTextDocument.getUri
    val pos = params.getPosition
    val line = pos.getLine
    val char = pos.getCharacter

    val found = originMap.maxBefore((line, char, Int.MaxValue)) match {
      case Some(((refLine, refStart, refEnd), (declLine, declStart, declEnd)))
        if refLine == line && refStart <= char && char <= refEnd =>
        val range = new Range(new Position(declLine, declStart), new Position(declLine, declEnd))
        val location = new Location(uri, range)
        Either.forLeft(Collections.singletonList(location))
      case _ =>
        MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Warning,
          s"No definition found for position: $pos"
        ))
        Either.forLeft(Collections.emptyList())
    }

    CompletableFuture.completedFuture(found)
  }*/
  override def definition(params: DefinitionParams): CompletableFuture[
    Either[java.util.List[_ <: Location], java.util.List[_ <: LocationLink]]
  ] = {
    val uri = params.getTextDocument.getUri
    val pos = params.getPosition
    val line = pos.getLine
    val char = pos.getCharacter

    val result: Either[java.util.List[_ <: Location], java.util.List[_ <: LocationLink]] =
      originMap.maxBefore((line, char, Int.MaxValue)) match {
        case Some(((refLine, refStart, refEnd), (declLine, declStart, declEnd)))
          if refLine == line && refStart <= char && char <= refEnd =>
          val range = new Range(new Position(declLine, declStart), new Position(declLine, declEnd))
          val location = new Location(uri, range)
          Either.forLeft(Collections.singletonList[Location](location))
        case _ =>
          MyLanguageServer.client.logMessage(new MessageParams(
            MessageType.Warning,
            s"No definition found for position: $pos"
          ))
          Either.forLeft(Collections.emptyList[Location]())
      }

    CompletableFuture.completedFuture(result)
  }
}
object LocalCollector {
  def collectLocals(root: Node[_]): Seq[Local[_]] = {
    val result = scala.collection.mutable.Buffer.empty[Local[_]]
    val stack = scala.collection.mutable.Stack[Node[_]](root)

    while (stack.nonEmpty) {
      val node = stack.pop()
      if (node.isInstanceOf[Local[_]]) {
        result += node.asInstanceOf[Local[_]]
      }
      stack.pushAll(node.subnodes)
    }

    result.toSeq
  }

  def hashLocalOrigins(locals: Seq[Local[_]]): Map[(Int, Int, Int), (Int, Int, Int)] = {
    locals.flatMap { local =>
      val declRangeOpt = local.ref.decl.o.find[PositionRange]
      val refRangeOpt = local.o.find[PositionRange]

      for {
        declRange <- declRangeOpt
        refRange <- refRangeOpt
        (startDeclCol, endDeclCol) <- declRange.startEndColIdx
        (startRefCol, endRefCol) <- refRange.startEndColIdx
      } yield {
        val declKey = (refRange.startLineIdx, startRefCol, endRefCol)
        val declValue = (declRange.startLineIdx, startDeclCol, endDeclCol)
        declKey -> declValue
      }
    }.toMap
  }
}