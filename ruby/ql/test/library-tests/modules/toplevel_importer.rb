def method_from_importer # called from toplevel_lib
end

require_relative 'toplevel_lib'

method_from_lib # should call method in toplevel_lib
