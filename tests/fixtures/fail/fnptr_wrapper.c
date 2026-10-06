void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void mf(void*p){free(p);}
int main(void){int*p=malloc(4);void(*f)(void*)=mf;f(p);free(p);return 0;}
