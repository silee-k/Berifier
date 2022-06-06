#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  int z = input();
  assume(x > 1);
  assume(y > 1);
  assume(z < 1);
  assert(x * y * z < 1);
  return 0;
}
