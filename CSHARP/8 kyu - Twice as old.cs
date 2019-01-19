using System;

namespace Solution
{
  public class TwiceAsOldSolution
  {
    public static int TwiceAsOld(int dadYears, int sonYears) =>
      Math.Abs(sonYears * 2 - dadYears);
  }
}
