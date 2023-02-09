package cuvee.util

import cuvee.StringOps

/** Identifier for expressions
  *
  * @param name
  *   String identifying the item
  * @param index
  *   Optional integer index
  */
case class Name(name: String, index: Option[Int] = None) {
  def withName(name_ : String) = Name(name_, index)
  def withIndex(index_ : Int) = Name(name, Some(index_))

  /** Convert the name into a label that may be given to a solver for instance.
    *
    * @return
    *   String of the form `name$index` or `name`, if there's no index.
    */
  def toLabel: String = name ~~ index
  override def toString: String = name __ index
}

object Name extends (String => Name) {
  implicit def stringToName(name: String): Name = {
    val idx = name lastIndexOf '$'
    if (idx < 0)
      Name(name, None)
    else
      name splitAt idx match {
        case (name_, id) =>
          id.substring(1).toIntOption match {
            case Some(index) =>
              Name(name_, Some(index))
            case None => 
              Name(name, None)
          }
      }
  }
  implicit def stringRenameToNameRename(f: String => String): (Name => Name) =
    name => name.withName(f(name.name))

  def apply(name: String) = Name(name, None)
}