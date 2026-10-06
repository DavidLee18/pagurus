void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void myfree(void*p){free(p);}
int main(void){int*p=malloc(4);myfree(p);myfree(p);return 0;}
