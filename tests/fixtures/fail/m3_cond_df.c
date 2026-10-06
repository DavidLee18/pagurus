/* FAIL: conditional free of the parameter is May-consume; treated as a move. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p, int c) {
    if (c)
        free(p);
}

int main(int argc, char **argv) {
    int *p = malloc(4);
    w(p, argc);
    free(p);
    return 0;
}
