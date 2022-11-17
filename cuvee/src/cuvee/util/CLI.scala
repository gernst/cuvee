package cuvee.util

object CLI {
  def askChoices[T](
      desc: String,
      choices: List[T],
      mustChoose: Boolean = false,
      default: Option[Int] = None,
      printfn: (String => Unit) = print
  ): Option[T] = {
    var result: Option[T] = None

    do {
      printfn(f"$desc\n")
      if (!mustChoose)
        if (default.getOrElse(0) < 0)
          printfn(f"< n>  None\n")
        else
          printfn(f"[ n]  None\n")

      for ((choice, idx) <- choices.zipWithIndex)
        if (default == Some(idx))
          printfn(f"<$idx%2d>  ${choice}\n")
        else
          printfn(f"[$idx%2d]  ${choice}\n")

      printfn("Your choice: ")
      scala.Console.flush()

      val input = scala.io.StdIn.readLine()

      if (input == "" && default.isDefined)
        return choices.lift(default.get)

      if (!mustChoose && input.toLowerCase == "n")
        return None

      result = input.toIntOption
        .filter(i => 0 <= i && i < choices.length)
        .map(idx => choices(idx))

    } while (result.isEmpty)

    result
  }
}
