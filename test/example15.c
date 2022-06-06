#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  int z = input();
  assume(x < z);
  while (x < z) {
    x++;
  }
  assume(y > z);
  while (y > z) {
    y--;
  }
  assert(x == y);
  return 0;
}
