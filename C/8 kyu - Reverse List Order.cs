using System.Collections.Generic;

public class Kata
{
  public static List<int> ReverseList(List<int> list)
  {
    List<int> newList = new List<int>(list);
    newList.Reverse();
    return newList;
  }
}
