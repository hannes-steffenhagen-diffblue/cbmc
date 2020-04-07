import os
import subprocess
import sys
import tempfile
import glob

this_script_dir = os.path.abspath(os.path.dirname(__file__))

TraceXsdSpec = os.path.abspath(os.path.join(this_script_dir, '..', '..', 'doc/assets/xml_spec.xsd'))

test_base_dir = os.path.abspath(os.path.join(this_script_dir, '..', 'cbmc'))

# some tests in the cbmc suite don't work for the trace checks for one reason or another
ExcludedTests = list(map(lambda s: os.path.join(test_base_dir, s), [
    # these tests except input from stdin
    'json-interface1/test_wrong_option.desc',
    'json-interface1/test.desc',
    'json-interface1/test_wrong_flag.desc',
    'xml-interface1/test_wrong_option.desc',
    'xml-interface1/test.desc',
    'xml-interface1/test_wrong_flag.desc',
    # these want --show-goto-functions instead of producing a trace
    'destructors/compound_literal.desc',
    'destructors/enter_lexical_block.desc',
    'reachability-slice-interproc2/test.desc',
    # this one wants show-properties instead producing a trace
    'show_properties1/test.desc',
    # program-only instead of trace
    'vla1/program-only.desc',
    'Quantifiers-simplify/simplify_not_forall.desc',
    # this one doesn't work for me locally at all
    # 'integer-assignments1/test.desc',
    # these test for invalid command line handling
    'bad_option/test_multiple.desc',
    'bad_option/test.desc',
    # this one produces XML intermingled with main XML output when used with --xml-ui
    'graphml_witness2/test.desc',
    # produces intermingled XML on the command line
    'coverage_report1/test.desc',
    'coverage_report1/paths.desc',
    'graphml_witness1/test.desc',
    'switch8/program-only.desc',
    # this uses json-ui (fails for a different reason actually, but should also
    #   fail because of command line incompatibility)
    'json1/test.desc',
    # uses show-goto-functions
    'reachability-slice/test.desc',
    'reachability-slice/test2.desc',
    'reachability-slice/test3.desc',
    'reachability-slice-interproc/test.desc',
    'unsigned1/test.desc',
    'reachability-slice-interproc3/test.desc',
    'sync_lock_release-1/symbol_per_type.desc',
    # this test is marked broken-smt-backend and doesn't work for me locally
    'integer-assignments1/test.desc'
]))

if len(sys.argv) != 2:
    sys.stderr.write('Usage: check.py <path-to-cbmc>')
CbmcPath = os.path.abspath(sys.argv[1])
XsdValidateJar = os.path.join(this_script_dir, 'validate-xsd/build/libs/validate-xsd-1.0-SNAPSHOT-uber.jar')


class ChangeDir:
    def __init__(self, change_to_wd):
        self.current_wd = os.getcwd()
        self.change_to_wd = change_to_wd

    def __enter__(self):
        os.chdir(self.change_to_wd)

    def __exit__(self, _type, _value, _tb):
        os.chdir(self.current_wd)


class TestSpec:
    def __init__(self, args, is_knownbug, is_future, is_thorough):
        self.args = args
        self.is_knownbug = is_knownbug
        self.is_future = is_future
        self.is_thorough = is_thorough


class Validator:
    def __init__(self, total_specs):
        self.failed_tests = []
        self.total_specs = total_specs
        self.total_test_count = 0

    def check_spec(self, spec_path):
        self.total_test_count += 1
        sys.stdout.write('*** Checking [{}/{}] {}... '.format(self.total_test_count, self.total_specs, spec_path))
        sys.stdout.flush()
        spec_dir = os.path.dirname(spec_path)
        spec = self.read_spec(spec_path)
        if spec.is_knownbug:
            print('[Skipping KNOWNBUG]')
            return
        elif spec.is_future:
            print('[Skipping FUTURE]')
            return
        elif spec.is_thorough:
            print('[Skipping THOROUGH]')
            return
        with ChangeDir(spec_dir):
            with tempfile.TemporaryFile() as trace_file:
                self.read_trace_into(trace_file, spec.args)
                trace_file.seek(0)
                self.check_trace(spec_path, trace_file)

    def read_trace_into(self, trace_file, args):
        subprocess.run([CbmcPath, '--trace', '--xml-ui'] + args,
                       stdout=trace_file)

    def check_trace(self, spec_path, trace_file):
        validate_result = subprocess.run(['java', '-jar', XsdValidateJar, TraceXsdSpec],
                                         stdin=trace_file,
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE)
        if validate_result.returncode == 0:
            print('[SUCCESS]')
        else:
            print('[FAILURE]')
            self.failed_tests.append(spec_path)
        sys.stdout.buffer.write(validate_result.stdout)
        sys.stdout.buffer.write(validate_result.stderr)

    def read_spec(self, spec_path):
        with open(spec_path) as spec_file:
            spec = spec_file.readline().split()
            source_file = spec_file.readline().strip()
            extra_args = spec_file.readline().split()
        is_future = 'FUTURE' in spec
        is_thorough = 'THOROUGH' in spec
        is_knownbug = 'KNOWNBUG' in spec
        return TestSpec(args=[source_file] + extra_args,
                        is_thorough=is_thorough,
                        is_future=is_future,
                        is_knownbug=is_knownbug)

    def has_failed_tests(self):
        return len(self.failed_tests) > 0

    def report(self):
        print('{}/{} tests succeed'.format(self.total_test_count - len(self.failed_tests), self.total_test_count))
        if self.has_failed_tests():
            print('Failed tests:')
            for spec in self.failed_tests:
                print(spec)


def run_gradle(args):
    with ChangeDir('validate-xsd'):
        if os.name == 'nt':
            subprocess.check_call(['cmd', '/c', 'gradlew.bat'] + args)
        else:
            subprocess.check_call(['./gradlew'] + args)


# ensure that the uberjar exists and is up to date
run_gradle(['uberjar'])

test_desc_files = list(
    filter(lambda s: s not in ExcludedTests, glob.glob(os.path.join(test_base_dir, '*/*.desc'))))
validator = Validator(total_specs=len(test_desc_files))
for spec in test_desc_files:
    validator.check_spec(spec)
validator.report()
if validator.has_failed_tests():
    sys.exit(1)
