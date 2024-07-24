func main()
{
        Int[] a;
        const Int alength;

        Int i = 1;
        while(i < alength)
        {
                a[i] = 1;
                i = i+1;
        }
	i = alength - 1;
	while (i >= 0)
	{
	  a[i] = a[i] -1;
	  i = i - 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
          (< pos alength)
          (<= alength (i main_end))
         )
       (= 0 (a main_end pos))
      )
   )
)
