plugins {
    id("kotlin-common")
    id("cli-tool")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-analysis"))
    implementation(project(":theta-xcfa"))
    implementation(project(":theta-xcfa-analysis"))
    implementation(project(":theta-c2xcfa"))
    implementation(project(":theta-solver-z3"))
    implementation(project(":theta-solver-smtlib"))
    implementation(project(":theta-solver"))
    implementation(project(":theta-c-frontend"))
    implementation(project(":theta-grammar"))
    implementation(project(":theta-xsts"))
    implementation(project(":theta-xsts-cli"))
    implementation("com.zaxxer:nuprocess:2.0.2")
    runtimeOnly("org.jetbrains.kotlin:kotlin-scripting-jsr223:1.7.10")
}

application {
    mainClassName = "hu.bme.mit.theta.xcfa.cli.XcfaCli"
}
