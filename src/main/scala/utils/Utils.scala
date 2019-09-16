package utils

import java.io.File

/**
  * @author Tianhan Lu
  */
object Utils {
  val SEPARATOR: String = File.separator
  val DESKTOP_PATH: String = System.getProperty("user.home") + SEPARATOR + "Desktop"
  val OUTPUT_DIR: String = DESKTOP_PATH + SEPARATOR + "outputs"

  def printRedString(s: String): Unit = println(Console.RED + s + Console.BLACK)

  def printRedString(o: Object): Unit = println(Console.RED + o.toString + Console.BLACK)

  def printGreenString(s: String): Unit = println(Console.GREEN + s + Console.BLACK)

  def printGreenString(o: Object): Unit = println(Console.GREEN + o.toString + Console.BLACK)

  def printYellowString(s: String): Unit = println(Console.YELLOW + s + Console.BLACK)

  def printYellowString(o: Object): Unit = println(Console.YELLOW + o.toString + Console.BLACK)

  def printBlueString(s: String): Unit = println(Console.BLUE + s + Console.BLACK)

  def printBlueString(o: Object): Unit = println(Console.BLUE + o.toString + Console.BLACK)

  def printMagentaString(s: String): Unit = println(Console.MAGENTA + s + Console.BLACK) // pink

  def printMagentaString(o: Object): Unit = println(Console.MAGENTA + o.toString + Console.BLACK) // pink

  def printCyanString(s: String): Unit = println(Console.CYAN + s + Console.BLACK) // light blue

  def printCyanString(o: Object): Unit = println(Console.CYAN + o.toString + Console.BLACK) // light blue

  def printReversedString(s: String): Unit = println(Console.REVERSED + s + Console.BLACK)

  def printReversedString(o: Object): Unit = println(Console.REVERSED + o.toString + Console.BLACK)

  def printPercentage(d: Double): Unit = print(("%.3f" format d) + "%")

  def getPercentage(d: Double): String = ("%.3f" format d * 100) + "%"

  def assertFalse(str: String): Unit = { Utils.printRedString(str); assert(false) }

  val NANO = 1000000000

  val MILLION = 1000000

  def genRandStr(len: Int=4): String = {
    assert(len>0)
    val r = new scala.util.Random()
    // val res = for (i <- 0 to r.nextInt(len)+1) yield r.nextPrintableChar
    var i = 0
    var res = ""
    while (i<len) {
      val ch = r.nextPrintableChar
      // if ((ch>='a' && ch<='z') || (ch>='A' && ch<='Z') || (ch>='0' && ch<='9')) {
      if (ch>='a' && ch<='z') {
        res = res + ch.toString
        i += 1
      }
    }
    res.foldLeft(""){ (acc, ch) => acc+ch }
  }
}