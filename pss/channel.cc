pool<channel_s> channel_1 {2}; 
class transfer : public action {
public:
transfer (const scope & p): action (this) {}
  input<data_buff_s> in_mem{this};
  output <data_buff_s> out_mem{this};
  lock<channel_s> channel {"channel"};
  constraint c {in_mem.data.size == out_mem.data.size};
};
type_decl<transfer> transfer t; 