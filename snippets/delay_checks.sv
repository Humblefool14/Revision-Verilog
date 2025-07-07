time delay_val;  // Use time type for delays

if (delay_val < 0 || $isunknown(delay_val)) 
    delay_val = 0;

delay_val = (delay_val < 0) ? 0 : delay_val;
