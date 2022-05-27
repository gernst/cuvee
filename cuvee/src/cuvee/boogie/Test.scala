package cuvee.boogie

import cuvee.util.Main
import cuvee.util.Run

object _test extends Run(Test, "test.bpl")

object Test extends Main {
  def main(args: Array[String]): Unit = {
    for (arg <- args) {
      val (cmds, st) = parse(arg)

      for (cmd <- cmds)
        println(cmd)
    }
  }
}
