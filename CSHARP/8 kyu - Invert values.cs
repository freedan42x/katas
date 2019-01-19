namespace Solution
{
  public static class ArraysInversion
  {
    public static int[] InvertValues(int[] input)
    {
      for (int i = 0; i < input.Length; i++)
      {
        input[i] = 0 - input[i];
      }
      return input;
    }
  }
}
