// Version d'OpenGL
#version 120

// Données d'entrée
attribute vec3 vertex_position;

// Fonction appelée pour chaque sommet
void main() {
        // Affectation de la position du sommet
        gl_Position = vec4(vertex_position, 1.);

        // Affectation de la taille du sommet (gros)
        // gl_PointSize = 10.0f;

        // On écrase en largeur d'un facteur 2
        // gl_Position.x /= 2;
}