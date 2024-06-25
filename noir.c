static size_t
number_len (int number)
{
  int mul;
  int count;

number_len:
  count = (int)1;
  mul = (int)10;
  goto comp_block;

comp_block:
  if (mul > number) goto then_block; else goto else_block;

then_block:
  return (size_t)count;

else_block:
  count += (int)1;
  mul *= (int)10;
  goto comp_block;
}

static char *
string (int number)
{
  size_t number_len;
  char * buffer;
  int index;
  int remainder;

str_conv:
  number_len = number_len (number);
  buffer = (char *)malloc (number_len (number));
  index = (int)number_len;
  index -= (int)1;
  goto build;

build:
  remainder = number % (int)10 + (int)48;
  number /= (int)10;
  buffer[index] = (char)remainder;
  index -= (int)1;
  if (number > (int)0) goto build; else goto end_block;

end_block:
  return buffer;
}

extern int
main ()
{
  char * str;
  int _0;

initial:
  str = string ((int)123);
  _0 = printf (((const char *)str));
  return (int)0;
}

static int
fib (int n)
{
fib_block:
  if (n < (int)2) goto then_block; else goto else_block;

then_block:
  return n;

else_block:
  return fib ((n - (int)1)) + fib ((n - (int)2));
}

