/* FAIL: a later use after a loop that may free is unsafe. */
void *malloc(unsigned long n);
void free(void *p);

void inspect(void *p) {
}

int main(void) {
    void *p = malloc(8);
    int i;
    for (i = 0; i < 1; i = i + 1) {
        free(p);
    }
    inspect(p);
    return 0;
}
