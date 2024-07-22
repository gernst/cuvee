datatype rope
  = leaf(text: string)
  | node(weight: int, left: rope, right: rope)

function repr(r: rope): string {
  match r {
    case leaf(text) =>
      text
    case node(weight, left, right) =>
      repr(left) + repr(right)
  }
}

predicate valid(r: rope) {
  match r {
    case leaf(text) =>
      true
    case node(weight, left, right) =>
      weight == |repr(left)| && valid(left) && valid(right)
  }
}

function length(r: rope): int {
  match r {
    case leaf(text) =>
      |text|
    case node(weight, left, right) =>
      weight + length(right)
  }
}

function concat(r1: rope, r2: rope): rope {
  node(length(r1), r1, r2)
}

lemma length_correct(r: rope)
  requires valid(r)
  ensures  length(r) == |repr(r)|
{
}

lemma concat_correct(r1: rope, r2: rope)
  requires valid(r1) && valid(r2)
  ensures  valid(concat(r1, r2))
  ensures  repr(concat(r1, r2)) == repr(r1) + repr(r2)
{
  length_correct(r1);
}

function take(r: rope, i: int): rope
  requires 0 <= i <= |repr(r)|
  requires valid(r)
{
  match r {
    case leaf(text) =>
      leaf(text[..i])
    case node(weight, left, right) =>
      if(i < weight)
      then
        var left_ := take(left, i);
        left_
      else if(i == weight)
        then
          left
        else
          var mid_ := take(right, i - weight);
          concat(left, mid_)
  }
}


function split(r: rope, i: int): (rope, rope)
  requires 0 <= i <= |repr(r)|
  requires valid(r)
{
  match r {
    case leaf(text) =>
      (leaf(text[..i]), leaf(text[i..]))
    case node(weight, left, right) =>
      if(i < weight)
      then
        var (left_, mid_) := split(left, i);
        (left_, concat(mid_, right))
      else if(i == weight)
        then
          (left, right)
        else
          var (mid_, right_) := split(right, i - weight);
          (concat(left, mid_), right_)
  }
}

lemma split_correct(r: rope, i: int)
  requires 0 <= i <= |repr(r)|
  requires valid(r)
  ensures  var (left, right) := split(r, i);
           |repr(left)| == i && repr(left) + repr(right) == repr(r) &&
           valid(left) && valid(right)
{
  match r {
    case leaf(_) =>

    case node(weight, left, right) =>
      if(i < weight) {
        var (left_, mid_) := split(left, i);
        concat_correct(mid_, right);
      }

      if(i > weight) {
        var (mid_, right_) := split(right, i - weight);
        concat_correct(left, mid_);
      }
  }
}

function delete(r: rope, i: int, len: int): rope
  requires valid(r)
  requires 0 <= i <= i + len <= |repr(r)|

{
  var (left_, rest_) := split(r, i);
  split_correct(r, i);
  var (mid_, right_) := split(rest_, len);
  concat(left_, right_)
}

lemma delete_correct(r: rope, i: int, len: int)
  requires valid(r)
  requires 0 <= i <= i + len <= |repr(r)|
  ensures var r_ := delete(r, i, len);
          repr(r_) == repr(r)[..i] + repr(r)[i+len..] && valid(r_)
{
  var (left_, rest_) := split(r, i);
  split_correct(r, i);
  var (mid_, right_) := split(rest_, len);
  split_correct(rest_, len);
  concat_correct(left_, right_);
}