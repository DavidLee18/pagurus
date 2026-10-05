/* Uses inside a loop must not consume the unique owner. */
void *malloc(unsigned long n);
void free(void *p);

void inspect(void *p) {
}

int main(void) {
    void *p = malloc(8);
    int i;
    for (i = 0; i < 3; i = i + 1) {
        inspect(p);
    }
    free(p);
    return 0;
}
