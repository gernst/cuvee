package cuvee.util

import java.io.FileInputStream
import collection.JavaConverters._

case class Yaml(value: Any) {
  def asBoolean = value match {
    case value: java.lang.Boolean =>
      value.booleanValue()
  }

  def asInt = value match {
    case value: java.lang.Integer =>
      value.intValue()
  }

  def asString = value match {
    case value: String =>
      value
  }

  def asMap = value match {
    case map: java.util.Map[String, Any] =>
      for ((key, value) <- map.asScala.toMap)
        yield (key, Yaml(value))
  }

  def asList = value match {
    case list: java.util.List[Any] =>
      for (value <- list.asScala.toList)
        yield Yaml(value)
  }

  def apply(key: String) = value match {
    case map: java.util.Map[String, Any] =>
      Yaml(map.get(key))
  }

  def get(key: String) = value match {
    case map: java.util.Map[String, Any] =>
      if (map.containsKey(key))
        Some(Yaml(map.get(key)))
      else
        None
  }
}

object Yaml {
  def load(path: String) = {
    val yaml = new org.yaml.snakeyaml.Yaml()
    val stream = new FileInputStream(path)
    Yaml(yaml.load[Any](stream))
  }
}
