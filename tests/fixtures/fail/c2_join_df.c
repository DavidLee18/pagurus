/* FAIL: joining NULL with malloc is not known-null; a second free is a DF
   on the malloc path. */
void *malloc(unsigned long n);
void free(void *p);

int main(int argc, char **argv) {
    int *p;
    if (argc > 1)
        p = NULL;
    else
        p = malloc(4);
    free(p);
    free(p);
    return 0;
}
