#include "verifier.h"

int main() {
  int x = input();
  int z = 0;
  if (x < z) {
    x++;
  }
  else if (x > z) {
    x--;
  } else {
    assert(x == z);
  }
}
