package lsp

import com.typesafe.scalalogging.LazyLogging
import io.circe.generic.auto._
import io.circe.parser._
import hre.io
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.{
  CompletionItem,
  Diagnostic,
  DiagnosticSeverity,
  Position,
  PublishDiagnosticsParams,
  Range,
  _,
}
import vct.col.ast.{
  Deref,
  InvokeConstructor,
  InvokeMethod,
  InvokeProcedure,
  InvokingNode,
  Local,
  ModelDeref,
  Node,
  Verification,
}
import vct.col.origin.{
  BlameCollector,
  Name,
  Origin,
  PositionRange,
  ReadableOrigin,
}
import vct.col.rewrite.Generation
import vct.lsp.LspMessages._
import vct.lsp.VerificationErrorsUtils.sendVerificationErrorDiagnostic
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
import scala.collection.concurrent.TrieMap
import scala.collection.immutable.TreeMap
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

class MyTextDocumentService extends TextDocumentService with LazyLogging {
  private val docs = TrieMap.empty[String, String]
  var parsingResults: Option[ParseResult[Nothing]] = None
  var resolutionResults: Option[Verification[_ <: Generation]] = None
  var originMap: TreeMap[(Int, Int, Int), (Int, Int, Int)] = TreeMap.empty
  private val dirty = TrieMap.empty[String, Boolean]
  private lazy val javaCompletions: List[CompletionItem] = loadCompletions(
    "lsp/language-server-java-c-matches.json"
  )
  private lazy val pvlCompletions: List[CompletionItem] = loadCompletions(
    "lsp/language-server-pvl-matches.json"
  )

  override def didOpen(params: DidOpenTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    docs(uri) = params.getTextDocument.getText
    dirty.put(uri, false)
    analyzeDocument(uri)
  }

  override def didSave(params: DidSaveTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    dirty.put(uri, false)
    analyzeDocument(uri)
  }

  override def didChange(params: DidChangeTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    val text = params.getContentChanges.get(0).getText
    docs(uri) = text
    dirty.put(uri, true)
    analyzeDocument(uri)
  }

  def isDirty(uri: String): Boolean = dirty.getOrElse(uri, false)

  override def didClose(params: DidCloseTextDocumentParams): Unit = {}

  override def completion(params: CompletionParams): CompletableFuture[
    Either[java.util.List[CompletionItem], CompletionList]
  ] = {
    val uri = params.getTextDocument.getUri
    val pos = params.getPosition
    val prefix = extractPrefix(docs.getOrElse(uri, ""), pos)

    val ext = uri.split("\\.").lastOption.getOrElse("")
    val pool =
      ext match {
        case "java" | "c" | "cpp" => javaCompletions
        case "pvl" => pvlCompletions
        case _ => javaCompletions ++ pvlCompletions
      }

    val jsonFiltered = pool.filter(_.getLabel.startsWith(prefix))

    val symbolCompletions: List[CompletionItem] = resolutionResults.toList
      .flatMap { res =>
        val uses = collectNameUses(res.tasks.head.program)
        uses.map { case (_, declOrigin) =>
          val rawName = declOrigin.getPreferredNameOrElse()
          val nameStr = formatName(rawName)
          val item = new CompletionItem(nameStr)
          item.setKind(CompletionItemKind.Variable)
          item
        }.groupBy(_.getLabel).values.map(_.head).toList
      }

    val allCompletions = (jsonFiltered ++ symbolCompletions)
      .filter(_.getLabel.startsWith(prefix))

    val list = new CompletionList(allCompletions.asJava)
    CompletableFuture.completedFuture(Either.forRight(list))
  }

  override def documentSymbol(params: DocumentSymbolParams) = null

  override def resolveCompletionItem(
      unresolved: CompletionItem
  ): CompletableFuture[CompletionItem] = null

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
          locationLink.setTargetSelectionRange(targetRange)

          Either.forRight(Collections.singletonList(locationLink))

        case _ =>
          showInfo(
            s"No definition found at line ${pos.getLine}, character ${pos.getCharacter}"
          )
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
      val uses = collectNameUses(resolvedProgram)
      originMap = TreeMap.from(hashNameUseOrigins(uses))
    } catch {
      case err: VerificationError.UserError =>
        val diagnostics = createDiagnostics(err)
        if (diagnostics.nonEmpty) {
          MyLanguageServer.client.publishDiagnostics(
            new PublishDiagnosticsParams(uri, diagnostics.asJava)
          )
        } else { sendVerificationErrorDiagnostic(uri, err) }

      case err: VerificationError =>
        sendVerificationErrorDiagnostic(uri, err)
        showError("Verification error")

      case ex: Exception => showError(s"Unexpected error: ${ex.getMessage}")
    }
  }

  private def loadCompletions(path: String): List[CompletionItem] = {
    case class Entry(`match`: String)

    Option(getClass.getClassLoader.getResourceAsStream(path)) match {
      case Some(stream) =>
        val src = scala.io.Source.fromInputStream(stream)
        val entries =
          try parse(src.mkString).flatMap(_.as[List[Entry]]).getOrElse(Nil)
          finally src.close()
        entries.distinctBy(_.`match`).map { e =>
          val it = new CompletionItem(e.`match`)
          it.setKind(CompletionItemKind.Keyword)
          it
        }
      case None =>
        showError(s"Failed to load completions JSON: $path")
        Nil
    }
  }
  private def collectLocals(root: Node[_]): Seq[Local[_]] = {
    val result = scala.collection.mutable.Buffer.empty[Local[_]]
    val stack = scala.collection.mutable.Stack[Node[_]](root)

    while (stack.nonEmpty) {
      val node = stack.pop()
      if (node.isInstanceOf[Local[_]]) { result += node.asInstanceOf[Local[_]] }
      stack.pushAll(node.subnodes)
    }
    result.toSeq
  }

  private def findNameInLine(
      lines: Array[String],
      name: String,
      lineIdx: Int,
      spanStart: Int,
      spanEnd: Int,
  ): (Int, Int) = {
    val line = lines(lineIdx)
    val s = spanStart.max(0).min(line.length)
    // make sure the “spanEnd” also doesn’t run off the line
    val eRaw = spanEnd.max(0).min(line.length)
    val sub = line.substring(s, eRaw)
    val m = raw"\b${Regex.quote(name)}\b".r.findFirstMatchIn(sub)
    val found = m.map(_.start + s).getOrElse(s)

    // clamp the computed end to line.length
    val endCol = (found + name.length).min(line.length)
    (found, endCol)
  }

  private def collectNameUses[T](root: Node[T]): Seq[(Origin, Origin)] = {
    val buf = mutable.Buffer.empty[(Origin, Origin)]
    val stack = mutable.Stack[Node[T]](root)

    while (stack.nonEmpty) {
      val n = stack.pop()
      n match {
        case l: Local[T] => buf += (l.o -> l.ref.decl.o)
        case d: Deref[T] => buf += (d.o -> d.ref.decl.o)
        case m: ModelDeref[T] => buf += (m.o -> m.ref.decl.o)
        case inv: InvokingNode[T] => buf += (inv.o -> inv.ref.decl.o)
        case other =>
          other.o.getPreferredName.foreach { _ => buf += (other.o -> other.o) }
      }
      // here n.subnodes: Seq[Node[T]], so it typechecks
      stack.pushAll(n.subnodes)
    }
    buf.toSeq
  }

  private def hashNameUseOrigins(
      uses: Seq[(Origin, Origin)]
  ): Map[(Int, Int, Int), (Int, Int, Int)] = {
    uses.flatMap { case (useO, declO) =>
      for {
        PositionRange(uLine, _, Some((uStartCol, uEndCol))) <- useO
          .find[PositionRange]
        PositionRange(dLine, _, Some((dStartCol, dEndCol))) <- declO
          .find[PositionRange]
      } yield {
        // just trust the span directly without scanning source lines
        (uLine, uStartCol, uEndCol) -> (dLine, dStartCol, dEndCol)
      }
    }.toMap
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

  private def formatName(name: Name): String =
    name match {
      case Name.Preferred(parts) => parts.mkString
      case Name.Required(n) => n
      case Name.Join(a, b) => a.toString + b.toString
    }
}
