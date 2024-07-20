class my_report_server extends uvm_report_server;

  // Factory registration
  `uvm_object_utils(my_report_server)

  // Constructor
  function new(string name = "my_report_server");
    super.new(name);
  endfunction

  // Override the compose_message function to customize message format
  virtual function string compose_message(
    uvm_severity severity,
    string name,
    string id,
    string message,
    string filename,
    int line
  );
    string composed_message;
    string time_str;

    // Get current simulation time
    $sformat(time_str, "%0t", $time);

    // Customize the message format
    composed_message = $sformatf("[%s][%s][%s][%s] %s (%s:%0d)",
                                 time_str,
                                 severity.name(),
                                 name,
                                 id,
                                 message,
                                 filename,
                                 line);

    return composed_message;
  endfunction

  // Override the report function to add custom behavior
  virtual function void report(
    uvm_severity severity,
    string name,
    string id,
    string message,
    int verbosity_level,
    string filename,
    int line,
    uvm_report_object client
  );
    // Add custom behavior here, e.g., logging to a file
    if (severity == UVM_ERROR || severity == UVM_FATAL) begin
      // Log errors and fatals to a file
      int fd = $fopen("error_log.txt", "a");
      $fdisplay(fd, compose_message(severity, name, id, message, filename, line));
      $fclose(fd);
    end

    // Call the base class implementation to maintain default behavior
    super.report(severity, name, id, message, verbosity_level, filename, line, client);
  endfunction

endclass


class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  function my_test :: new(string name = "my_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void my_test :: start_of_simulation_phase(uvm_phase phase);
    my_report_server server;
    server = my_report_server::type_id::create("my_server");
    uvm_report_server::set_server(server);
  endfunction

endclass