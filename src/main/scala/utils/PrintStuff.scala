package utils

/**
  * @author Tianhan Lu
  */
object PrintStuff {
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

  def assertFalse(str: String): Unit = { PrintStuff.printRedString(str); assert(false) }
}