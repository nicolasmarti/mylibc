#include "basetype.h"
#include "string.h"

#include <stdio.h>

// just a test for the lib

int main(int argc, char** argv, char** arge)
{
  printf("%zd\n", my_strlen((const string_t)"doudou"));

  return 0;
}
