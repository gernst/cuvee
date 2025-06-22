package cuvee

import java.io.File

package object test {
  def find(dir: File, suffix: String, exclude: List[String]): List[File] = {
    dir.listFiles.toList.flatMap {
      case file if file.getName endsWith suffix =>
        List(file)

      case file if exclude contains file.getName =>
        Nil

      case file if file.isDirectory =>
        find(file, suffix, exclude)
    }
  }
}
