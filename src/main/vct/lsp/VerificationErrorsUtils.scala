package vct.lsp

import lsp.MyLanguageServer
import org.eclipse.lsp4j.{
  Diagnostic,
  DiagnosticSeverity,
  Position,
  PublishDiagnosticsParams,
  Range,
}
import vct.col.ast.Node
import vct.col.check.CheckError
import vct.col.origin.{Origin, PositionRange}
import vct.lsp.LspMessages.showError
import vct.main.stages.HasCheckErrors
import vct.result.VerificationError

import scala.jdk.CollectionConverters._

object VerificationErrorsUtils {
  def sendVerificationErrorDiagnostic(
      uri: String,
      err: VerificationError,
  ): Unit =
    err match {

      case hc: HasCheckErrors =>
        val diagnostics = hc.errors.flatMap { chk: CheckError =>
          findOrigin(chk).map { origin =>
            val range: Range = origin.find[PositionRange].map {
              case PositionRange(sl, el, Some((sc, ec))) =>
                new Range(new Position(sl, sc), new Position(el, ec))
              case PositionRange(sl, el, None) =>
                new Range(new Position(sl, 0), new Position(el, 0))
            }.getOrElse(new Range(new Position(0, 0), new Position(0, 0)))

            val diag =
              new Diagnostic(
                range,
                chk.message(_.o),
                DiagnosticSeverity.Error,
                "VerCors",
              )
            diag
          }
        }
        MyLanguageServer.client.publishDiagnostics(
          new PublishDiagnosticsParams(uri, diagnostics.asJava)
        )

      case otherErr =>
        findOrigin(otherErr) match {
          case Some(origin) =>
            val range = originToRange(origin)
            val diag = createVerificationErrorDiagnostic(otherErr, range)
            MyLanguageServer.client.publishDiagnostics(
              new PublishDiagnosticsParams(uri, List(diag).asJava)
            )
          case None =>
            showError(
              s"Verification failed, verification error without position, error type: ${otherErr.getClass.getSimpleName}"
            )
            publishNoPositionError(uri, otherErr)
        }
    }

  private def publishNoPositionError(
      uri: String,
      err: VerificationError,
  ): Unit = {
    val diagnostic = new Diagnostic()
    diagnostic.setSeverity(DiagnosticSeverity.Error)
    diagnostic.setMessage(err.getMessage)
    diagnostic.setRange(new Range(new Position(0, 0), new Position(0, 0)))
    diagnostic.setSource("VerCors")

    MyLanguageServer.client.publishDiagnostics(
      new PublishDiagnosticsParams(uri, List(diagnostic).asJava)
    )
  }

  private def originToRange(origin: Origin) = {
    origin.find[PositionRange].map {
      case PositionRange(startLine, endLine, Some((startCol, endCol))) =>
        new Range(
          new Position(startLine, startCol),
          new Position(endLine, endCol),
        )
      case PositionRange(startLine, endLine, None) =>
        new Range(new Position(startLine, 0), new Position(endLine, 0))
    }.getOrElse(new Range(new Position(0, 0), new Position(0, 0)))
  }

  private def createVerificationErrorDiagnostic(
      err: VerificationError,
      range: Range,
  ) = {
    val diagnostic = new Diagnostic()
    diagnostic.setSeverity(DiagnosticSeverity.Error)
    diagnostic.setRange(range)
    diagnostic.setSource("VerCors")
    diagnostic.setMessage(err.getMessage)
    diagnostic
  }

  private def findOrigin(obj: Any): Option[Origin] = {
    def tryGet(methodName: String): Option[Origin] = {
      obj.getClass.getMethods.find(m =>
        m.getName == methodName && m.getParameterCount == 0 &&
          classOf[Origin].isAssignableFrom(m.getReturnType)
      ).flatMap { method =>
        try Some(method.invoke(obj).asInstanceOf[Origin])
        catch { case _: Throwable => None }
      }
    }

    tryGet("o").orElse(tryGet("origin")).orElse {
      obj.getClass.getDeclaredFields
        .find(f => classOf[Origin].isAssignableFrom(f.getType))
        .flatMap { field =>
          field.setAccessible(true)
          try Some(field.get(obj).asInstanceOf[Origin])
          catch { case _: Throwable => None }
        }
    }.orElse {
      obj.getClass.getDeclaredFields
        .find(f => classOf[Node[_]].isAssignableFrom(f.getType))
        .flatMap { field =>
          field.setAccessible(true)
          try {
            val node = field.get(obj).asInstanceOf[Node[_]]
            Some(node.o)
          } catch { case _: Throwable => None }
        }
    }
  }
}
