void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void vc(void*p,...){free(p);}
int main(void){int*p=malloc(4);vc(p,1);free(p);return 0;}
