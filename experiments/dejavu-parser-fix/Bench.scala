import java.io.FileReader

object Bench {
  def main(args: Array[String]): Unit = {
    val which = args(0); val file = args(1); val timeoutMs = args(2).toLong
    val watchdog = new Thread(() => { Thread.sleep(timeoutMs); System.out.println("TIMEOUT"); System.exit(124) })
    watchdog.setDaemon(true); watchdog.start()
    val t0 = System.nanoTime
    val ok = which match {
      case "packrat" =>
        val p = new dejavu.ParserPackrat
        p.parseAll(p.document, new FileReader(file)).successful
      case "wide" =>
        val p = new dejavu.ParserWide
        p.parseAll(p.document, new FileReader(file)).successful
      case _ =>
        val p = new dejavu.Parser
        p.parseAll(p.document, new FileReader(file)).successful
    }
    val ms = (System.nanoTime - t0) / 1e6
    println(f"$ms%.1f ms  parsed=$ok")
  }
}
