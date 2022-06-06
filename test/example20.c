#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  int z;
  assume(y == -x);
  if (x < 0) {
    z = y + 10;
  } else if (x == 0) {
    z = x + 0;
  } else {
    z = y + 2 * x;
  }
  assert(z >= 0);
  return 0;
}
