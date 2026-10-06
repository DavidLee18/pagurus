void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=calloc(1,4);free(p);free(p);return 0;}
