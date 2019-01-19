using System.Linq;

public class Kata
{
  public static int[] Maps(int[] x) =>
    x.Select(e => e * 2).ToArray();
}
