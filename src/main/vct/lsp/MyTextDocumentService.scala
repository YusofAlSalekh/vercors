package lsp

import io.circe.generic.auto._, io.circe.parser._
import com.typesafe.scalalogging.LazyLogging
import io.circe.parser._
import hre.io

import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.{LanguageClient, TextDocumentService}
import org.eclipse.lsp4j.{
  CompletionItem,
  Diagnostic,
  DiagnosticSeverity,
  Position,
  PublishDiagnosticsParams,
  Range,
  _,
}

import vct.col.ast.{Local, Node, Verification}
import vct.col.origin.{
  BlameCollector,
  Name,
  NameStrategy,
  Origin,
  PositionRange,
  PreferredName,
  ReadableOrigin,
}
import vct.col.rewrite.Generation
import vct.main.stages.{Parsing, Resolution}
import vct.options.Options
import vct.options.types.PathOrStd
import vct.parsers.ParseResult
import vct.parsers.transform.ConstantBlameProvider
import vct.result.VerificationError

import java.net.URI
import java.nio.file.Paths
import java.util.Collections
import java.util.concurrent.CompletableFuture
import scala.collection.immutable.TreeMap
import scala.io.Source
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex
import scala.collection.immutable.TreeMap
import scala.collection.mutable

class MyTextDocumentService extends TextDocumentService with LazyLogging {
  private val docs = scala.collection.concurrent.TrieMap.empty[String, String]
  var parsingResults: Option[ParseResult[Nothing]] = None
  var resolutionResults: Option[Verification[_ <: Generation]] = None
  var originMap: TreeMap[(Int, Int, Int), (Int, Int, Int)] = TreeMap.empty

  override def didOpen(params: DidOpenTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    docs(uri) = params.getTextDocument.getText
    analyzeDocument(uri)
  }

  override def didSave(params: DidSaveTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    MyLanguageServer.client
      .showMessage(new MessageParams(MessageType.Info, s"Document saved"))
    analyzeDocument(uri)
  }

  override def didChange(params: DidChangeTextDocumentParams): Unit = {
    /*
    val text = params.getContentChanges.get(0).getText
  /*  val diagnostics = validateText(text)
    val paramsDiag =
      new PublishDiagnosticsParams(
        params.getTextDocument.getUri,
        diagnostics.asJava,
      )
    if (MyLanguageServer.client != null) {
      MyLanguageServer.client.publishDiagnostics(paramsDiag)
    }*/*/
    val uri = params.getTextDocument.getUri
    val text = params.getContentChanges.get(0).getText
    docs(uri) = text
    analyzeDocument(uri)

  }

  override def didClose(params: DidCloseTextDocumentParams): Unit = {
    /*  MyLanguageServer.client.logMessage(new MessageParams(
      MessageType.Log,
      s"Document closed: ${params.getTextDocument.getUri}",
    ))*/

  }

  private lazy val allCompletions: List[CompletionItem] = loadAllCompletions()

  private def loadAllCompletions(): List[CompletionItem] = {
    case class Entry(`match`: String)

    def load(path: String): List[Entry] = {
      val source = scala.io.Source.fromInputStream(getClass.getClassLoader.getResourceAsStream(path))
      val content = try source.mkString finally source.close()

      try parse(content).flatMap(_.as[List[Entry]]).getOrElse(Nil)
    }

    val javaEntries = load(
      "lsp/language-server-java-c-matches.json"
    )
    val pvlEntries = load(
      "lsp/language-server-pvl-matches.json"
    )

    (javaEntries ++ pvlEntries).distinctBy(_.`match`).map { e =>
      val it = new CompletionItem(e.`match`)
      it.setKind(CompletionItemKind.Keyword)
      it
    }
  }

  private def extractPrefix(text: String, pos: Position): String = {
    val lines = text.split("\r?\n", -1)
    if (pos.getLine >= lines.length)
      return ""
    val line = lines(pos.getLine)
    val idx = pos.getCharacter.min(line.length)
    line.substring(0, idx).reverse
      .takeWhile(ch => ch.isLetterOrDigit || ch == '_').reverse
  }

  override def completion(params: CompletionParams): CompletableFuture[
    Either[java.util.List[CompletionItem], CompletionList]
  ] = {
    val uri = params.getTextDocument.getUri
    val pos = params.getPosition
    val prefix = extractPrefix(docs.getOrElse(uri, ""), pos)
    val filtered = allCompletions.filter(_.getLabel.startsWith(prefix))
    val list = new CompletionList(filtered.asJava)
    CompletableFuture.completedFuture(Either.forRight(list))
  }

  override def documentSymbol(params: DocumentSymbolParams) = null

  override def resolveCompletionItem(
      unresolved: CompletionItem
  ): CompletableFuture[CompletionItem] = null

  private def analyzeDocument(uri: String): Unit = {
    MyLanguageServer.client.publishDiagnostics(
      new PublishDiagnosticsParams(uri, Collections.emptyList())
    )
    val path = Paths.get(new URI(uri))
    val options = Options().copy(inputs = List(PathOrStd.Path(path)))

    try {
      val collector = BlameCollector()
      val blameProvider = ConstantBlameProvider(collector)

      parsingResults = Some(
        Parsing.ofOptions(options, blameProvider).run(options.inputs)
      )
      resolutionResults = Some(
        Resolution.ofOptions(options, blameProvider).run(parsingResults.get)
      )

      val resolvedProgram = resolutionResults.get.tasks.head.program
      val locals: Seq[Local[_]] = collectLocals(resolvedProgram)
      originMap = TreeMap.from(hashLocalOrigins(locals))

      // Clear any previous diagnostics (optional)
      // MyLanguageServer.client.publishDiagnostics(new PublishDiagnosticsParams(uri, Collections.emptyList()))
    } catch {
      case err: VerificationError.UserError =>
        /* MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Error,
          s"User error during parsing/resolution: ${err.text}",
        ))*/
        val diagnostics = createDiagnostics(err)
        MyLanguageServer.client.publishDiagnostics(
          new PublishDiagnosticsParams(uri, diagnostics.asJava)
        )

      // add diagnostics
      case err: VerificationError.SystemError =>
        MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Error,
          s"Verification error: ${err.text}",
        ))

      // add diagnostics
      case ex: Exception =>
        MyLanguageServer.client.logMessage(new MessageParams(
          MessageType.Error,
          s"Unexpected error: ${ex.getMessage}",
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

  override def definition(params: DefinitionParams): CompletableFuture[
    Either[java.util.List[_ <: Location], java.util.List[_ <: LocationLink]]
  ] = {
    val uri = params.getTextDocument.getUri
    val pos = params.getPosition
    val line = pos.getLine
    val char = pos.getCharacter

    val result: Either[java.util.List[_ <: Location], java.util.List[
      _ <: LocationLink
    ]] =
      originMap.maxBefore((line, char, Int.MaxValue)) match {
        case Some(((refLine, refStart, refEnd), (declLine, declStart, declEnd)))
            if refLine == line && refStart <= char && char <= refEnd =>
          val originRange =
            new Range(
              new Position(refLine, refStart),
              new Position(refLine, refEnd),
            )
          val targetRange =
            new Range(
              new Position(declLine, declStart),
              new Position(declLine, declEnd),
            )

          val locationLink = new LocationLink()
          locationLink.setOriginSelectionRange(originRange)
          locationLink.setTargetUri(uri)
          locationLink.setTargetRange(targetRange)
          locationLink
            .setTargetSelectionRange(targetRange) // could be improved later

          Either.forRight(Collections.singletonList(locationLink))

        case _ =>
          MyLanguageServer.client.showMessage(new MessageParams(
            MessageType.Info,
            s"No definition found at line ${pos.getLine}, character ${pos.getCharacter}",
          ))
          Either.forRight(Collections.emptyList())
      }
    CompletableFuture.completedFuture(result)
  }

  case class ParsedError(
      message: String,
      startLine: Int,
      startCol: Int,
      endLine: Int,
      endCol: Int,
  )

  private def createDiagnostics(
      err: VerificationError.UserError
  ): List[Diagnostic] = {
    extractFirstParsedError(err).toList.map { pe =>
      val diagnostic = new Diagnostic()
      diagnostic.setSeverity(DiagnosticSeverity.Error)
      diagnostic.setMessage(pe.message)
      diagnostic.setRange(new Range(
        new Position(pe.startLine, pe.startCol),
        new Position(pe.endLine, pe.endCol),
      ))
      diagnostic
    }
  }

  private def extractFirstParsedError(
      err: VerificationError.UserError
  ): Option[ParsedError] =
    err match {
      case pe: vct.parsers.err.ParseError => extractFromParseError(pe)

      case vct.parsers.err.ParseErrors(errors) =>
        errors.iterator.map(extractFromParseError).collectFirst {
          case Some(pe) => pe
        }

      case _ => None
    }

  private def extractFromParseError(
      pe: vct.parsers.err.ParseError
  ): Option[ParsedError] = {
    pe.origin.find[PositionRange].flatMap { pos =>
      pos.startEndColIdx.map { case (startCol, endCol) =>
        ParsedError(
          message = pe.message,
          startLine = pos.startLineIdx,
          startCol = startCol,
          endLine = pos.endLineIdx,
          endCol = endCol,
        )
      }
    }
  }

  def collectLocals(root: Node[_]): Seq[Local[_]] = {
    val result = scala.collection.mutable.Buffer.empty[Local[_]]
    val stack = scala.collection.mutable.Stack[Node[_]](root)

    while (stack.nonEmpty) {
      val node = stack.pop()
      if (node.isInstanceOf[Local[_]]) { result += node.asInstanceOf[Local[_]] }
      stack.pushAll(node.subnodes)
    }
    result.toSeq
  }

  def hashLocalOrigins(
      locals: Seq[Local[_]]
  ): Map[(Int, Int, Int), (Int, Int, Int)] = {
    locals.flatMap { local =>
      val declOrigin = local.ref.decl.o
      val declRangeOpt = declOrigin.find[PositionRange]
      val refRangeOpt = local.o.find[PositionRange]
      val nameOpt = declOrigin.getPreferredName
      val readableOpt = declOrigin.find[ReadableOrigin].map(_.readable)

      for {
        declRange <- declRangeOpt
        refRange <- refRangeOpt
        name <- nameOpt
        readable <- readableOpt
        (startDeclCol, _) <- declRange.startEndColIdx
        (startRefCol, endRefCol) <- refRange.startEndColIdx
      } yield {
        val nameText = formatName(name)
        val nameStartCol = findNameStartCol(
          declRange,
          readable,
          startDeclCol,
          nameText,
        )
        val nameEndCol = nameStartCol + nameText.length

        val declKey = (refRange.startLineIdx, startRefCol, endRefCol)
        val declValue = (declRange.startLineIdx, nameStartCol, nameEndCol)

        declKey -> declValue
      }
    }.toMap
  }

  private def findNameStartCol(
      declRange: PositionRange,
      readable: io.Readable,
      startDeclCol: Int,
      nameText: String,
  ): Int = {
    val lineText = readable.readLines()(declRange.startLineIdx)
    val nameRegex = raw"\b${Regex.quote(nameText)}\b".r
    val searchRegion = lineText.drop(startDeclCol)
    val matchOpt = nameRegex.findFirstMatchIn(searchRegion)
    val nameStartCol = matchOpt.map(_.start + startDeclCol)
      .getOrElse(startDeclCol)
    nameStartCol
  }

  private def formatName(name: Name): String =
    name match {
      case Name.Preferred(parts) => parts.mkString
      case Name.Required(n) => n
      case Name.Join(a, b) => a.toString + b.toString
    }

}
