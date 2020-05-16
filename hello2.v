module Add_half(output c_out,sum,input a,b);
    xor (sum,a,b);
    and (c_out,a,b);
end module
