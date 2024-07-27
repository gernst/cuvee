import mill._
import mill.scalalib._

object easyparse extends ScalaModule {
  def millSourcePath = super.millSourcePath / "easyparse"
  def scalaVersion = "2.13.12"
  def ivyDeps = Agg(ivy"com.lihaoyi::sourcecode:0.2.7")
}

object cuvee extends ScalaModule {
  def scalaVersion = "2.13.12"
  def forkArgs = Seq("-Xss32m")

  def moduleDeps = Seq(easyparse)

  def mainClass = Some("cuvee.Cuvee")

  def unmanagedClasspath = T {
    if (!os.exists(millSourcePath / "lib")) Agg()
    else Agg.from(os.list(millSourcePath / "lib").map(PathRef(_)))
  }

  def ivyDeps = Agg(
    ivy"com.lihaoyi::sourcecode:0.3.1",
    ivy"com.lihaoyi::fastparse:3.0.2",
    ivy"com.lihaoyi::pythonparse:3.0.2",
    ivy"org.yaml:snakeyaml:2.2"
  )
}

object tests extends ScalaModule {
  def scalaVersion = cuvee.scalaVersion
  def forkArgs = cuvee.forkArgs
  def moduleDeps = Seq(cuvee)
  def mainClass = Some("tests.Tests")
}
