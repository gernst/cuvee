import mill._
import mill.scalalib._

object easyparse extends ScalaModule {
  def millSourcePath = super.millSourcePath / "easyparse"
  def scalaVersion = "2.13.8"
  def ivyDeps = Agg(ivy"com.lihaoyi::sourcecode:0.2.7")
}

object cuvee extends ScalaModule {
  def scalaVersion = "2.13.8"
  def forkArgs = Seq("-Xss32m")

  def moduleDeps = Seq(easyparse)

  def mainClass = Some("cuvee.Cuvee")

  def ivyDeps = Agg(
    ivy"com.lihaoyi::sourcecode:0.2.0",
    ivy"com.lihaoyi::fastparse:2.2.2",
    ivy"com.lihaoyi::pythonparse:2.3.0"
  )
}

object tests extends ScalaModule {
  def scalaVersion = cuvee.scalaVersion
  def forkArgs = cuvee.forkArgs
  def moduleDeps = Seq(cuvee)
  def mainClass = Some("tests.Tests")
}
