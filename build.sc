import mill._
import mill.scalalib._

object easyparse extends ScalaModule {
  def millSourcePath = super.millSourcePath / "arse"
  def scalaVersion = "2.13.8"
  def ivyDeps = Agg(ivy"com.lihaoyi::sourcecode:0.2.7")
}

object cuvee extends ScalaModule {
  def scalaVersion = "2.13.8"
  def forkArgs = Seq("-Xss32m")

  def moduleDeps = Seq(easyparse)

  def mainClass = Some("cuvee.Cuvee")
}
