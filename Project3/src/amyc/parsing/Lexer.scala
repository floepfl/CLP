package amyc
package parsing

import utils._
import scala.io.Source
import java.io.File

// The lexer for Amy.
// Transforms an iterator coming from scala.io.Source to a stream of (Char, Position),
// then uses a functional approach to consume the stream.
object Lexer extends Pipeline[List[File], Stream[Token]] {
  import Tokens._

  /** Maps a string s to the corresponding keyword,
    * or None if it corresponds to no keyword
    */
  private def keywords(s: String): Option[Token] = s match {
    case "abstract" => Some(ABSTRACT())
    case "Boolean"  => Some(BOOLEAN())
    case "case"     => Some(CASE())
    case "class"    => Some(CLASS())
    case "def"      => Some(DEF())
    case "else"     => Some(ELSE())
    case "error"    => Some(ERROR())
    case "extends"  => Some(EXTENDS())
    case "false"    => Some(FALSE())
    case "if"       => Some(IF())
    case "Int"      => Some(INT())
    case "match"    => Some(MATCH())
    case "object"   => Some(OBJECT())
    case "String"   => Some(STRING())
    case "true"     => Some(TRUE())
    case "Unit"     => Some(UNIT())
    case "val"      => Some(VAL())
    case _          => None
  }

  private def lexFile(ctx: Context)(f: File): Stream[Token] = {
    import ctx.reporter._

    // Special character which represents the end of an input file
    val EndOfFile: Char = scala.Char.MaxValue

    val source = Source.fromFile(f)

    // Useful type alias:
    // The input to the lexer will be a stream of characters,
    // along with their positions in the files
    type Input = (Char, Position)

    def mkPos(i: Int) = Position.fromFile(f, i)

    // The input to the lexer
    val inputStream: Stream[Input] =
      source.toStream.map(c => (c, mkPos(source.pos))) #::: Stream((EndOfFile, mkPos(source.pos)))

    /** Gets rid of whitespaces and comments and calls readToken to get the next token.
      * Returns the first token and the remaining input that did not get consumed
      */
    @scala.annotation.tailrec
    def nextToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream
      val l = stream.map(_._1).toList
      // Use with care!
      def nextChar = rest.head._1

      if (Character.isWhitespace(currentChar)) {
        nextToken(stream.dropWhile { case (c, _) => Character.isWhitespace(c) })
      } else if (currentChar == '/' && nextChar == '/') {
        val str = rest.tail.dropWhile { case (c, _) => (c != '\n' && c != '\r' && c != EndOfFile) }
        if (str.head._1 == EndOfFile) {
          readToken(str)
        } else {
          nextToken(str.tail)
        }
      } else if (currentChar == '/' && nextChar == '*') {
        def inner(stream: Stream[Input]): Stream[Input] = {
          val str = stream.dropWhile { case (c, _) => c != '*' }
          if (str.isEmpty) {
            Stream.empty
          } else if (str.tail.head._1 == '/') {
            str.tail.tail
          } else {
            inner(str.tail)
          }
        }

        val str = inner(rest.tail)
        if (str.isEmpty) {
          ctx.reporter.error("'*/' expected")
          (BAD().setPos(currentPos), str)
        } else {
          nextToken(str)
        }
      } else {
        readToken(stream)
      }
    }

    /** Reads the next token from the stream. Assumes no whitespace or comments at the beginning.
      * Returns the first token and the remaining input that did not get consumed.
      */
    def readToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream

      // Use with care!
      def nextChar = rest.head._1

      // Returns input token with correct position and uses up one character of the stream
      def useOne(t: Token) = (t.setPos(currentPos), rest)

      // Returns input token with correct position and uses up two characters of the stream
      def useTwo(t: Token) = (t.setPos(currentPos), rest.tail)

      currentChar match {
        case `EndOfFile` => useOne(EOF())

        // Reserved word or Identifier
        case _ if Character.isLetter(currentChar) =>
          val (wordLetters, afterWord) = stream.span { case (ch, _) =>
            Character.isLetterOrDigit(ch) || ch == '_'
          }
          val word = wordLetters.map(_._1).mkString
          // Hint: Decide if it's a letter or reserved word (use our infrastructure!),
          // and return the correct token, along with the remaining input stream.
          // Make sure you set the correct position for the token.
          /*   if(!Character.isWhitespace(afterWord.head._1)) {
               (BAD, )
               ctx.reporter.("Invalid variable name", )
             }*/
          if (keywords(word).isDefined) {
            (keywords(word).get.setPos(currentPos), afterWord)
          } else {
            (ID(word).setPos(currentPos), afterWord)
          }
        // Int literal
        case _ if Character.isDigit(currentChar) =>
          val (beforeInteger, afterInteger) = stream.span { case (ch, _) =>
            Character.isDigit(ch)
          }

          val int = BigInt(beforeInteger.map(_._1).mkString)
          if (int.isValidInt) {
            (INTLIT(int.toInt).setPos(currentPos), afterInteger)
          } else {
            error("Overflow from integer value", beforeInteger.head._2)
            (BAD().setPos(currentPos), afterInteger)
          }
        // Hint: Use a strategy similar to the previous example.
        // Make sure you fail for integers that do not fit 32 bits.
        // String literal
        case '"' =>
          val (string, afterString) = stream.tail.span { case (ch, _) =>
            ch != '"'
          }
          val list = string.map(_._1).toList
          if (list.foldLeft(false) { case (acc, el) => if (el == '\r' || el == '\n') acc || true else acc || false }) {
            error("Invalid String format. New line is not a valid character in a String", string.head._2)
            if(afterString.isEmpty) {
              (BAD().setPos(currentPos), Stream.empty)
            } else {
              (BAD().setPos(currentPos), afterString.tail)
            }
          } else {
            if(afterString.isEmpty) {
              if(string.contains('"')) {
                (EOF().setPos(currentPos), Stream.empty)
              } else {
                error("Expected '' ", currentPos)
                (BAD().setPos(currentPos), Stream.empty)
              }
            } else {
              (STRINGLIT(string.map(_._1).mkString).setPos(currentPos), afterString.tail)
            }
          }

        case _ =>
          currentChar match {
            case ';' => useOne(SEMICOLON()) // ;
            case '+' => {
              if (rest.head._1 == '+') {
                useTwo(CONCAT())
              } else {
                useOne(PLUS())
              }
            }
            case '-' => useOne(MINUS()) // -
            case '*' => useOne(TIMES()) // *
            case '/' => useOne(DIV()) // /
            case '%' => useOne(MOD()) // %
            case '<' => {
              if (rest.head._1 == '=') {
                useTwo(LESSEQUALS())
              } else {
                useOne(LESSTHAN())
              }
            }
            case '&' => {
              if (rest.head._1 == '&') {
                useTwo(AND())
              } else {
                error("& expected", rest.head._2)
                useOne(BAD())
              }
            }
            case '|' => {
              if (rest.head._1 == '|') {
                useTwo(OR())
              } else {
                error("| expected", rest.head._2)
                useOne(BAD())
              }
            }
            case '=' => {
              val c = rest.head._1
              if (c == '=') {
                useTwo(EQUALS())
              } else if (c == '>') {
                useTwo(RARROW())
              } else {
                useOne(EQSIGN())
              }
            }
            case '!' => useOne(BANG()) // !
            case '{' => useOne(LBRACE()) // {
            case '}' => useOne(RBRACE()) // }
            case '(' => useOne(LPAREN()) // (
            case ')' => useOne(RPAREN()) // )
            case ',' => useOne(COMMA()) // ,
            case ':' => useOne(COLON()) // :
            case '.' => useOne(DOT()) // .
            case '_' => useOne(UNDERSCORE()) // _
            case _ => {
              error("Invalid char", currentPos)
              useOne(BAD())
            }
          }
      }
    }

      // To lex a file, call nextToken() until it returns the empty Stream as "rest"
      def tokenStream(s: Stream[Input]): Stream[Token] = {
        if (s.isEmpty) Stream()
        else {
          val (token, rest) = nextToken(s)
          token #:: tokenStream(rest)
        }
      }

      tokenStream(inputStream)
    }


    // Lexing all input files means putting the tokens from each file one after the other
    def run(ctx: Context)(files: List[File]): Stream[Token] = {
      files.toStream flatMap lexFile(ctx)
    }
  }

  /** Extracts all tokens from input and displays them */
  object DisplayTokens extends Pipeline[Stream[Token], Unit] {
    def run(ctx: Context)(tokens: Stream[Token]): Unit = {
      tokens.toList foreach { t => println(s"$t(${t.position.withoutFile})") }
    }
  }
