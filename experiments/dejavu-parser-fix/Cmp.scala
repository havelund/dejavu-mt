import java.io.FileReader
import scala.io.Source

object Cmp {
  def main(args: Array[String]): Unit = {
    val file = args(0)
    val src = Source.fromFile(file).mkString
    val pw = new dejavu.ParserWide
    val pp = new dejavu.ParserPackrat
    val rw = pw.parseAll(pw.document, src)
    val rp = pp.parseAll(pp.document, src)
    (rw.successful, rp.successful) match {
      case (true, true) =>
        val same = rw.get.toString == rp.get.toString
        println(s"both parse; ASTs identical: $same")
        dejavu.SymbolTable.reset()
        println(s"wellformed under wide scope: ${rp.get.isWellformed}")
      case other => println(s"parse success (wide, packrat) = $other")
    }
  }
}
