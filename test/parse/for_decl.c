int main(void)
{
    int sum = 0;
    for (int i = 0; i < 5; ++i)
    {
        sum += i;
        continue;
    }
    return sum;
}