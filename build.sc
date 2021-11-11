import mill._
import mill.scalalib._

object cuvee extends ScalaModule {
  def scalaVersion = "2.13.7"
  def forkArgs = Seq("-Xss32m")

  def mainClass = Some("cuvee.Cuvee")
}
