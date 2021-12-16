package cuvee.util

trait Main {
  def main(args: Array[String]): Unit
}

class Run(what: Main, args: String*) extends Main {
  def main(args: Array[String]) =
    what main args.toArray
}
