/*
 * This file is the main configuration for the gradle build system.
 * It allows to run the test suite and build a jar for distribution.
 *
 * Author Malte Mues (@mmuesly)
 * Created August 2019
 */

plugins {
    `java`
}

allprojects {
    apply(plugin = "java-library")
    version = "0.9.10.4"
    repositories {
        jcenter()
        mavenCentral()
    }
    dependencies{
        // Use JUnit test framework
        testImplementation("junit:junit:4.12")
    }
}

sourceSets {
    main {
        java {
            setSrcDirs(listOf("SMT/src/"))
        }
        resources {
            setSrcDirs(listOf("SMT/logics", "SMT/solvers"))
        }
    }
    test {
        java{
            setSrcDirs(listOf("SMTTests/src", "SMT/test"))
        }
        resources {
            setSrcDirs(listOf("SMTTests/tests"))
        }
    }
}
