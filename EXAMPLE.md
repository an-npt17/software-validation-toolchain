# 1. Start with natural language requirements

cat > requirements/auth_system.txt \<< 'EOF'

# Authentication System Requirements

FR-1: The system shall authenticate users within 2 seconds
FR-2: Password must be at least 8 characters
FR-3: Account shall lock after 3 failed attempts

SR-1: Passwords shall be encrypted before storage
SR-2: Session tokens must expire after 30 minutes
EOF

# 2. Analyze requirements quality

analyze-requirements requirements/auth_system.txt --report

# Output shows:

# - Quality score for each requirement

# - Ambiguous words detected

# - Missing verifiable criteria

# - Suggestions for improvement

# 3. Generate UML state machine

cat > models/auth_state.puml \<< 'EOF'
@startuml
\[*\] --> Idle
Idle --> Authenticating : enter_credentials
Authenticating --> Authenticated : valid [attempts < 3]
Authenticating --> Failed : invalid [attempts < 3]
Failed --> Authenticating : retry
Authenticating --> Locked : invalid [attempts >= 3]
Authenticated --> \[*\]
Locked --> [\*]
@enduml
EOF

# 4. Generate diagram

plantuml models/auth_state.puml

# Creates auth_state.png

# 5. Verify state machine with TLA+

# (Write TLA+ spec based on diagram)

# 6. Generate ACSL from requirements

nl-to-acsl "Password must be at least 8 characters" \
--function validate_password \
--output specs/password.acsl

# 7. Implement in C with ACSL

cat > src/auth.c \<< 'EOF'
#include \<string.h>

/\*@
requires \\valid_read(password + (0..strlen(password)));
requires strlen(password) >= 8;
ensures \\result == 1;
\*/
int validate_password(const char \*password) {
return strlen(password) >= 8 ? 1 : 0;
}
EOF

# 8. Verify implementation

verify-all src/auth.c

# 9. Generate traceability report

# Requirements → Models → Code → Verification Results
