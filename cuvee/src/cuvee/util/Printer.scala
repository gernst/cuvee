package cuvee.util

/** A trait for a syntax representation */
trait Syntax {
  /** Converts this representation into a textual format.
    *
    * The format generated can be controlled by the @param
    *
    * @param p Defines the format to use
    * @return Textual representation of this object
    */
  def lines(implicit p: cuvee.util.Printer): List[String] = p.lines(this)
}

/** A trait for implementing pretty printers */
trait Printer {
  /** Converts a language-dependent internal representation of a program / proof
    * to a textual representation in the target language of the printer.
    *
    * @param repr The internal representation of the program
    * @return Representation of the input in the target language
    */
  def lines(repr: Any): List[String]
}