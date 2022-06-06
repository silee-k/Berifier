#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  int z = input();
  while (x < z) {
    x++;
  }
  while (y > z) {
    y--;
  }
  assert(x == y);
  return 0;
}
