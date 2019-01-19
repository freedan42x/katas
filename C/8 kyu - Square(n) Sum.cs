using System.Linq;

public static class Kata
{
  public static int SquareSum(int[] n) =>
    n.Select(e => e * e).Sum();
}
