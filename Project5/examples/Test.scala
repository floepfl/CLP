object test {
  val l: L.List = L.Cons(5, L.Cons(-5, L.Cons(-1, L.Cons(0, L.Cons(10, L.Nil())))));
  l match {
    case 3 => Std.printString("")
    case true => Std.printString("")
    case "HJello" => Std.printString("")
  }
}